module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicSectionPullback
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPullback
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrCycleClasses
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreCycleTransport
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibrePrincipalDivisor

/-!
# Degrees of special fibres are preserved by proper dominant morphisms

Let `R` be a discrete valuation ring with generic point `η` and closed point `s`, and let
`g : V ⟶ V'` be a proper dominant morphism of integral schemes locally of finite type over
`Spec R`. Assume that the generic point of `V` lies on the generic fibre and has dimension `r`
there. Then both `V` and `V'` are dominated by their generic fibres, hence flat over `R`, and
the cycle `[V_κ]_r` of the whole special fibre is the principal divisor `div_V(π)` of a
uniformizer `π` of `R`, read as a rational function on `V`.

The content of this file is that proper pushforward carries the one to the other:

  `g_* [V_κ]_r = [R(V) : R(V')] · [V'_κ]_r`.

This is Stacks 02RT, `g_* div_V(f) = div_{V'}(Nm(f))`, applied to the rational function `π`.
That function comes from the base, so it is the image of the corresponding function on `V'`
under the extension of function fields, its norm is therefore `π^d` with
`d = [R(V) : R(V')]`, and `div_{V'}(π^d) = d · div_{V'}(π) = d · [V'_κ]_r`. The multiplicity
`d` is exactly the weight with which the generic point of the generic fibre of `V` enters the
proper pushforward of cycles on generic fibres, which is how the statement is phrased: it is
`Stacks.Chow.fiberPushforwardWeight` at that point.

Two reductions make the argument possible. First, everything is compared on the total spaces
`V` and `V'` rather than on the special fibres, where the Chow situation is the one on the
spectrum of the residue field; the translation is
`Stacks.Chow.fiberSubschemeCycle_bot_apply_fiberι` and `Stacks.Chow.properPushforward_fiber_apply`.
Second, the dimension index is never rewritten: the delta-dimension of `V` over `R` is `r + 1`, so
the principal divisor lives in degree `(r + 1) - 1`, and the coefficientwise statements are used to
cross between that index and `r`.

When the generic point of the generic fibre of `V'` has dimension different from `r` the weight
is zero by definition, and the pushforward vanishes as well: the dimension of a point of the
generic fibre can only drop along `g`, while a point of the special fibre contributing to the
pushforward would force it to be at least `r`.

## Main results

* `Stacks.Chow.properPushforward_fiberSubschemeCycle_bot` — **the degree of the special fibre
  is multiplied by the degree of the function field extension.**

## Implementation notes

Several small auxiliary statements are proved first because the main argument needs them in a
shape no existing lemma has: `Stacks.Chow.schemeDeltaDimension_dvrChowSituation_int` is the
delta-dimension computation with an integer rather than a natural dimension, which is what the
vanishing case needs since the dimension of the generic point of the generic fibre of `V'` is
not known to be a natural number there; and
`Stacks.Chow.cycleAssociatedToClosedSubscheme_apply_congr_index` together with
`Stacks.Chow.properPushforward_apply_congr_index` let an equal dimension index be substituted
coefficientwise, which avoids rewriting inside the dependent type `Stacks.Chow.CycleGroup`.

The Chow situation on the spectrum of the residue field at the closed point is never written
out: instance resolution would have to identify `PrimeSpectrum R` with the carrier of `Spec R`
at reducible transparency to find the field structure. Everything on the special fibre is
phrased through `Stacks.Chow.fiberProperPushforward`, `Stacks.Chow.fiberSubschemeCycle` and
`Stacks.Chow.FiberCycleGroup`, which hide it.

## References

* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RO](https://stacks.math.columbia.edu/tag/02RO)
* [Stacks Project, Tag 0H4M](https://stacks.math.columbia.edu/tag/0H4M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Changing the dimension index -/

/-- The cycle of a closed subscheme is unchanged, coefficientwise, when its dimension index is
replaced by an equal integer: the index enters only through the equation it is tested against. -/
theorem cycleAssociatedToClosedSubscheme_apply_congr_index (C : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (i : Z ⟶ X) [IsClosedImmersion i]
    {k k' : ℤ} (hk : k = k') (x : X) :
    (cycleAssociatedToClosedSubscheme C f i k : AlgebraicCycle X ℤ) x =
      (cycleAssociatedToClosedSubscheme C f i k' : AlgebraicCycle X ℤ) x := by
  rw [hk]

/-- The coefficients of a proper pushforward depend on the cycle only through its coefficients,
not through the dimension index of the group it is taken in: the coefficient formula of
Stacks 02R4 does not mention that index. -/
theorem properPushforward_apply_congr_index (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsProper f] (hf : f ≫ sY = sX) {k k' : ℤ} (c : CycleGroup C sX k)
    (c' : CycleGroup C sX k')
    (hc : ∀ x : X, (c : AlgebraicCycle X ℤ) x = (c' : AlgebraicCycle X ℤ) x) (y : Y) :
    (properPushforward C sX sY f hf k c : AlgebraicCycle Y ℤ) y =
      (properPushforward C sX sY f hf k' c' : AlgebraicCycle Y ℤ) y := by
  rw [properPushforward_apply, properPushforward_apply]
  exact finsum_mem_congr rfl fun x _ ↦ by rw [hc x]

/-! ### Dominance and dimensions of fibres -/

/-- A morphism whose image contains the generic point of an irreducible target is dominant: the
closure of that point is already the whole target. -/
theorem isDominant_of_base_eq_genericPoint {X S : Scheme.{u}} [IrreducibleSpace S]
    (f : X ⟶ S) {x : X} (h : f.base x = genericPoint S) : IsDominant f := by
  rw [isDominant_iff]
  intro y
  have hmem : genericPoint S ∈ Set.range f.base := ⟨x, h⟩
  exact closure_mono (Set.singleton_subset_iff.mpr hmem)
    (specializes_iff_mem_closure.mp (genericPoint_specializes y))

/-- The dimension of a point of a fibre can only drop along a morphism over the base: the
relative dimension over the spectrum of the residue field of the base point grows by the
transcendence degree of the residue field extension, which is nonnegative. -/
theorem fiberPointDimension_inducedFiberMap_le {S X Y : Scheme.{u}} (sX : X ⟶ S)
    [LocallyOfFiniteType sX] (sY : Y ⟶ S) [LocallyOfFiniteType sY] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (hf : f ≫ sY = sX) (s : S) (x : sX.fiber s) :
    fiberPointDimension sY s ((inducedFiberMap sX sY f hf s).base x) ≤
      fiberPointDimension sX s x := by
  have : LocallyOfFiniteType (sY.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (pullback.snd sY (S.fromSpecResidueField s)); infer_instance
  have : LocallyOfFiniteType (inducedFiberMap sX sY f hf s) :=
    MorphismProperty.of_isPullback (isPullback_inducedFiberMap sX sY f hf s) inferInstance
  have h := relativeDimension_comp_eq_add_trdeg
    (fieldChowSituation (S.residueField s)).dimensionFunction
    (sY.fiberToSpecResidueField s) (inducedFiberMap sX sY f hf s) x
  rw [inducedFiberMap_fiberToSpecResidueField] at h
  have h' : fiberPointDimension sX s x =
      fiberPointDimension sY s ((inducedFiberMap sX sY f hf s).base x) +
        (Cardinal.toNat (residueTrdeg (inducedFiberMap sX sY f hf s) x) : ℤ) := h
  omega

/-! ### The two points of the spectrum of a discrete valuation ring -/

section Dvr

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The closed point of the spectrum of a discrete valuation ring is not its generic point: the
maximal ideal is nonzero and the generic point carries the zero ideal. -/
theorem closedPoint_ne_genericPoint (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] :
    (IsLocalRing.closedPoint R : ↥(Spec (CommRingCat.of R))) ≠
      genericPoint (Spec (CommRingCat.of R)) := by
  intro h
  refine maximalIdeal_ne_bot_of_isDiscreteValuationRing R ?_
  have h2 := congrArg (fun x : ↥(Spec (CommRingCat.of R)) ↦ (x : PrimeSpectrum R).asIdeal) h
  rw [asIdeal_genericPoint_spec] at h2
  exact h2

/-- The delta-dimension over `R` of an irreducible scheme whose generic point lies on the
generic fibre is one more than the dimension of that point in the generic fibre. This is
`Stacks.Chow.schemeDeltaDimension_dvrChowSituation` with the dimension allowed to be any
integer rather than a natural number. -/
theorem schemeDeltaDimension_dvrChowSituation_int {V : Scheme.{u}} (sV : V ⟶ Spec (.of R))
    [LocallyOfFiniteType sV] [IrreducibleSpace V] {m : ℤ}
    (ξ : sV.fiber (genericPoint (Spec (.of R))))
    (hξ : (sV.fiberι (genericPoint (Spec (.of R)))).base ξ = genericPoint V)
    (hdim : fiberPointDimension sV (genericPoint (Spec (.of R))) ξ = m) :
    schemeDeltaDimension (dvrChowSituation R) sV = ((m + 1 : ℤ) : EInt) := by
  rw [schemeDeltaDimension_eq_genericPoint, ← hξ,
    relativeDimension_dvrChowSituation_genericPoint, hdim]
  exact congrArg (fun z : ℤ ↦ (z : EInt)) (add_comm 1 m)

/-! ### A uniformizer along a dominant morphism -/

/-- A uniformizer of the base, read as a rational function, is compatible with a dominant
morphism over the base: the rational function it determines on the source is the image under
the extension of function fields of the one it determines on the target. -/
theorem dominantFunctionFieldMap_dvrUniformizerFunctionField {V V' : Scheme.{u}} [IsIntegral V]
    [IsIntegral V'] (sV' : V' ⟶ Spec (.of R)) (g : V ⟶ V') [IsDominant g] (π : R) :
    dominantFunctionFieldMap g (dvrUniformizerFunctionField sV' π) =
      dvrUniformizerFunctionField (g ≫ sV') π := by
  have : Nonempty ((⊤ : V.Opens) : Type u) := ⟨⟨Classical.arbitrary V, trivial⟩⟩
  have : Nonempty ((⊤ : V'.Opens) : Type u) := ⟨⟨Classical.arbitrary V', trivial⟩⟩
  have hle : (⊤ : V.Opens) ≤ g ⁻¹ᵁ (⊤ : V'.Opens) := by simp
  have hc : Stacks.Models.chartHom sV' (⊤ : V'.Opens) ≫ g.appLE (⊤ : V'.Opens) (⊤ : V.Opens) hle
      = Stacks.Models.chartHom (g ≫ sV') (⊤ : V.Opens) := by
    dsimp only [Stacks.Models.chartHom]
    rw [Category.assoc, Scheme.Hom.appLE_comp_appLE g sV' ⊤ ⊤ ⊤ (by simp) hle]
  have happ : (g.appLE (⊤ : V'.Opens) (⊤ : V.Opens) hle).hom
      ((Stacks.Models.chartHom sV' (⊤ : V'.Opens)).hom π)
      = (Stacks.Models.chartHom (g ≫ sV') (⊤ : V.Opens)).hom π :=
    congrArg (fun ψ : CommRingCat.of R ⟶ Γ(V, (⊤ : V.Opens)) ↦ ψ.hom π) hc
  have h := DFunLike.congr_fun (appLE_germToFunctionField_commutes g (⊤ : V'.Opens)
    (⊤ : V.Opens) hle) ((Stacks.Models.chartHom sV' (⊤ : V'.Opens)).hom π)
  simp only [RingHom.comp_apply] at h
  rw [← germToFunctionField_chartHom (g ≫ sV') π ⊤, ← germToFunctionField_chartHom sV' π ⊤,
    ← happ]
  exact h.symm

/-! ### Residue degrees on the generic fibre -/

omit [IsDiscreteValuationRing R] in
/-- The residue degree of the morphism induced on generic fibres, at a point lying over the
generic point of the source, is the residue degree of the morphism itself at that generic
point: the two inclusions of fibres are preimmersions, so they contribute nothing. -/
theorem residueDegree_inducedFiberMap_genericPoint {V V' : Scheme.{u}} [IrreducibleSpace V]
    (sV : V ⟶ Spec (.of R)) (sV' : V' ⟶ Spec (.of R)) (g : V ⟶ V') (hg : g ≫ sV' = sV)
    (ξ : sV.fiber (genericPoint (Spec (.of R))))
    (hξ : (sV.fiberι (genericPoint (Spec (.of R)))).base ξ = genericPoint V) :
    (inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).residueDegree ξ =
      g.residueDegree (genericPoint V) := by
  have h1 := residueDegree_comp (sV.fiberι (genericPoint (Spec (.of R)))) g ξ
  have h2 := residueDegree_comp (inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R))))
    (sV'.fiberι (genericPoint (Spec (.of R)))) ξ
  rw [residueDegree_eq_one_of_isPreimmersion (sV.fiberι (genericPoint (Spec (.of R)))) ξ,
    mul_one, hξ] at h1
  rw [residueDegree_eq_one_of_isPreimmersion (sV'.fiberι (genericPoint (Spec (.of R)))) _,
    one_mul] at h2
  rw [← h2, inducedFiberMap_fiberι]
  exact h1

/-! ### The degree of a special fibre under a proper dominant morphism -/

/-- **The degree of a special fibre is multiplied by the degree of the function field
extension.** Let `g : V ⟶ V'` be a proper dominant morphism of integral schemes locally of
finite type over a discrete valuation ring `R`, and suppose the generic point of `V` lies on
the generic fibre with dimension `r` there. Then the proper pushforward along the induced
morphism of special fibres sends the cycle of the whole special fibre of `V` to the
corresponding multiple of the cycle of the whole special fibre of `V'`, the multiple being the
weight with which the generic point of the generic fibre of `V` enters the pushforward of
cycles on generic fibres.

Both special fibres are principal divisors of a uniformizer of `R`, read as a rational function
on the respective total space, so this is Stacks 02RT together with the computation of the norm
of an element coming from the base. -/
theorem properPushforward_fiberSubschemeCycle_bot
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {V V' : Scheme.{u}}
    (sV : V ⟶ Spec (.of R)) [LocallyOfFiniteType sV] [IsIntegral V]
    (sV' : V' ⟶ Spec (.of R)) [LocallyOfFiniteType sV'] [IsIntegral V']
    (g : V ⟶ V') [IsProper g] [IsDominant g] (hg : g ≫ sV' = sV) (r : ℕ)
    (ξ : sV.fiber (genericPoint (Spec (.of R))))
    (hξ : (sV.fiberι (genericPoint (Spec (.of R)))).base ξ = genericPoint V)
    (hdim : fiberPointDimension sV (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    fiberProperPushforward sV sV' g hg (IsLocalRing.closedPoint R) r
        (fiberSubschemeCycle sV (IsLocalRing.closedPoint R) r ⊥) =
      fiberPushforwardWeight sV sV' g hg (genericPoint (Spec (.of R))) ξ •
        fiberSubschemeCycle sV' (IsLocalRing.closedPoint R) r ⊥ := by
  classical
  -- the generic points of `V` and `V'` lie over the generic point of `Spec R`
  have hbaseV : sV.base (genericPoint V) = genericPoint (Spec (.of R)) := by
    rw [← hξ]; exact base_fiberι sV (genericPoint (Spec (.of R))) ξ
  have hdomV : IsDominant sV := isDominant_of_base_eq_genericPoint sV hbaseV
  have hdomV' : IsDominant sV' := by
    have : IsDominant (g ≫ sV') := by rw [hg]; exact hdomV
    exact IsDominant.of_comp g sV'
  have hgη : g.base (genericPoint V) = genericPoint V' :=
    Stacks.Divisors.base_genericPoint_of_isDominant g
  have hbaseV' : sV'.base (genericPoint V') = genericPoint (Spec (.of R)) := by
    rw [← hgη]
    have h := congrArg (fun φ : V ⟶ Spec (.of R) ↦ φ.base (genericPoint V)) hg
    simpa using h.trans hbaseV
  -- the image of `ξ` on the generic fibre of `V'`
  have hξ' : (sV'.fiberι (genericPoint (Spec (.of R)))).base
      ((inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).base ξ) = genericPoint V' := by
    rw [inducedFiberMap_fiberι_base, hξ, hgη]
  have hn' : schemeDeltaDimension (dvrChowSituation R) sV' =
      ((fiberPointDimension sV' (genericPoint (Spec (.of R)))
        ((inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).base ξ) + 1 : ℤ) : EInt) :=
    schemeDeltaDimension_dvrChowSituation_int sV' _ hξ' rfl
  have hle : fiberPointDimension sV' (genericPoint (Spec (.of R)))
      ((inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).base ξ) ≤ (r : ℤ) := by
    have h := fiberPointDimension_inducedFiberMap_le sV sV' g hg
      (genericPoint (Spec (.of R))) ξ
    omega
  -- the cycle of the special fibre of `V`, read on the total space
  have hcd : ∀ v : sV.fiber (IsLocalRing.closedPoint R),
      (fiberSubschemeCycle sV (IsLocalRing.closedPoint R) r ⊥ :
          AlgebraicCycle (sV.fiber (IsLocalRing.closedPoint R)) ℤ) v =
        (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
            ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ) :
          AlgebraicCycle V ℤ) ((sV.fiberι (IsLocalRing.closedPoint R)).base v) :=
    fun v ↦ fiberSubschemeCycle_bot_apply_fiberι sV ξ hξ hdim v
  have hstep1 := fun z ↦ properPushforward_fiber_apply sV sV' g hg r
    (fiberSubschemeCycle sV (IsLocalRing.closedPoint R) r ⊥)
    (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
      ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ)) hcd z
  by_cases hcase : fiberPointDimension sV' (genericPoint (Spec (.of R)))
      ((inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).base ξ) = (r : ℤ)
  · -- the weight is the degree of the residue field extension at the generic point
    have hweq : fiberPointDimension sV (genericPoint (Spec (.of R))) ξ =
        fiberPointDimension sV' (genericPoint (Spec (.of R)))
          ((inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).base ξ) := by
      rw [hdim, hcase]
    have hw : fiberPushforwardWeight sV sV' g hg (genericPoint (Spec (.of R))) ξ =
        (g.residueDegree (genericPoint V) : ℤ) := by
      unfold fiberPushforwardWeight
      rw [ite_eq_left hweq, residueDegree_inducedFiberMap_genericPoint sV sV' g hg ξ hξ]
    have : Flat sV := flat_of_isIntegral_of_isDominant sV
    have : Flat sV' := flat_of_isIntegral_of_isDominant sV'
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hnV : schemeDeltaDimension (dvrChowSituation R) sV = (((r : ℤ) + 1 : ℤ) : EInt) :=
      schemeDeltaDimension_dvrChowSituation_int sV ξ hξ hdim
    have hnV' : schemeDeltaDimension (dvrChowSituation R) sV' = (((r : ℤ) + 1 : ℤ) : EInt) := by
      rw [hn', hcase]
    have hVcyc := cycleAssociatedToClosedSubscheme_fiberι_ker_eq_principalDivisorCycle sV hnV hπ
    have hV'cyc := cycleAssociatedToClosedSubscheme_fiberι_ker_eq_principalDivisorCycle sV' hnV' hπ
    have hune : dvrUniformizerFunctionField sV' π ≠ 0 :=
      dvrUniformizerFunctionField_ne_zero sV' hπ
    let : Algebra V'.functionField V.functionField := (dominantFunctionFieldMap g).toAlgebra
    have hu : algebraMap V'.functionField V.functionField (dvrUniformizerFunctionField sV' π)
        = dvrUniformizerFunctionField sV π := by
      rw [RingHom.algebraMap_toAlgebra, ← hg]
      exact dominantFunctionFieldMap_dvrUniformizerFunctionField sV' g π
    have hpp : properPushforward (dvrChowSituation R) sV sV' g hg ((r : ℤ) + 1 - 1)
          (principalDivisorCycle (dvrChowSituation R) sV hnV
            (algebraMap V'.functionField V.functionField (dvrUniformizerFunctionField sV' π)))
        = (Module.finrank V'.functionField V.functionField : ℤ) •
          principalDivisorCycle (dvrChowSituation R) sV' hnV'
            (dvrUniformizerFunctionField sV' π) :=
      properPushforward_principalDivisorCycle_algebraMap (dvrChowSituation R) sV sV' hnV hnV' g hg
        (dvrUniformizerFunctionField sV' π) hune
    have hmain : properPushforward (dvrChowSituation R) sV sV' g hg ((r : ℤ) + 1 - 1)
          (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
            ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι ((r : ℤ) + 1 - 1))
        = (Module.finrank V'.functionField V.functionField : ℤ) •
          cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV'
            ((sV'.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι ((r : ℤ) + 1 - 1) := by
      rw [hVcyc, hV'cyc, ← hu]
      exact hpp
    have hfr : (Module.finrank V'.functionField V.functionField : ℤ)
        = (g.residueDegree (genericPoint V) : ℤ) :=
      congrArg (fun n : ℕ ↦ (n : ℤ)) (finrank_functionField_eq_residueDegree g)
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    have hstep2 := properPushforward_apply_congr_index (dvrChowSituation R) sV sV' g hg
      (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
        ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ))
      (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
        ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι ((r : ℤ) + 1 - 1))
      (fun x ↦ cycleAssociatedToClosedSubscheme_apply_congr_index (dvrChowSituation R) sV _
        (by ring) x)
      ((sV'.fiberι (IsLocalRing.closedPoint R)).base z)
    have hstep3 := congrArg
      (fun c : CycleGroup (dvrChowSituation R) sV' ((r : ℤ) + 1 - 1) ↦
        (c : AlgebraicCycle V' ℤ) ((sV'.fiberι (IsLocalRing.closedPoint R)).base z)) hmain
    have hstep4 := cycleAssociatedToClosedSubscheme_apply_congr_index (dvrChowSituation R) sV'
      ((sV'.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι
      (show ((r : ℤ) + 1 - 1) = (r : ℤ) by ring)
      ((sV'.fiberι (IsLocalRing.closedPoint R)).base z)
    have hstep5 := fiberSubschemeCycle_bot_apply_fiberι sV' (r := r) _ hξ' hcase z
    simp only at hstep3
    rw [hstep1 z, hstep2, hstep3, hw, hfr]
    simp [hstep4, hstep5]
  · -- the weight is zero and the pushforward vanishes
    have hne : ¬ (fiberPointDimension sV (genericPoint (Spec (.of R))) ξ =
        fiberPointDimension sV' (genericPoint (Spec (.of R)))
          ((inducedFiberMap sV sV' g hg (genericPoint (Spec (.of R)))).base ξ)) := by
      intro hc
      exact hcase (by rw [← hc, hdim])
    have hw : fiberPushforwardWeight sV sV' g hg (genericPoint (Spec (.of R))) ξ = 0 := by
      unfold fiberPushforwardWeight
      exact ite_eq_right hne
    rw [hw, zero_smul]
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun z ↦ ?_)
    have hdcyc : ∀ x : V, (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
          ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ) :
            AlgebraicCycle V ℤ) x ≠ 0 →
        relativeDimension (dvrChowSituation R).dimensionFunction sV x = (r : ℤ) :=
      (mem_cyclesOfDimension_iff_forall_point (dvrChowSituation R) sV (r : ℤ) _).mp
        (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
          ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ)).2
    have hyne : (sV'.fiberι (IsLocalRing.closedPoint R)).base z ≠ genericPoint V' := by
      intro hy
      have hys := base_fiberι sV' (IsLocalRing.closedPoint R) z
      rw [hy, hbaseV'] at hys
      exact closedPoint_ne_genericPoint R hys.symm
    have hterm : ∀ x ∈ g.base ⁻¹' {(sV'.fiberι (IsLocalRing.closedPoint R)).base z},
        (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
            ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ) :
          AlgebraicCycle V ℤ) x *
          (if relativeDimension (dvrChowSituation R).dimensionFunction sV x =
              relativeDimension (dvrChowSituation R).dimensionFunction sV' (g.base x)
            then (g.residueDegree x : ℤ) else 0) = 0 := by
      intro x hx
      by_cases hd : (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
          ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ) :
            AlgebraicCycle V ℤ) x = 0
      · rw [hd, zero_mul]
      by_cases hif : relativeDimension (dvrChowSituation R).dimensionFunction sV x =
          relativeDimension (dvrChowSituation R).dimensionFunction sV' (g.base x)
      · exfalso
        have hrx := hdcyc x hd
        have hxy : g.base x = (sV'.fiberι (IsLocalRing.closedPoint R)).base z := hx
        have hb := relativeDimension_le_sub_one_of_ne_genericPoint (dvrChowSituation R) sV'
          hn' hyne
        rw [← hxy, ← hif, hrx] at hb
        exact hcase (by omega)
      · rw [ite_eq_right hif, mul_zero]
    rw [hstep1 z, properPushforward_apply, finsum_mem_congr rfl hterm]
    simp

end Dvr

end Stacks.Chow

end
