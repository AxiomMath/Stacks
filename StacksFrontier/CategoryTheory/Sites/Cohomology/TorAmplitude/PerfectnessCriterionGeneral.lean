module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.TruncatingApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature

/-!
# The perfectness criterion of Stacks 08G7 on the diagonal `RingedSite.{u, u, u}`

Let `(C, O)` be a ringed site and let `T` be a derived tensor product on `D(O)`. An object of
`D(O)` with Tor amplitude in `[a, b]` for `T`, with `a ≤ b`, which is `(a - 1)`-pseudo-coherent,
is perfect.

That is `Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.PerfectnessCriterion`, proved there at
`RingedSite.{0, 0, 0}`. This file proves it on the diagonal `RingedSite.{u, u, u}`, the seat of
the monoidal development of Stacks 0FPT and of Stacks 0FPY. The proof is the base proof with `0`
replaced by `u`, and the five auxiliary statements it reads at universe `0` are restated at an
arbitrary universe alongside it:

* `SheafOfModules.isStrictlyPerfect_truncGE_general` (and `isZero_truncGE_X_general`), the
  canonical truncation in degrees `≥ r`;
* `Stacks.SheafOfModules.isStrictlyPerfect_stupidTrunc_general`, the brutal truncation;
* `Stacks.SheafOfModules.isFinitePresentation_opcycles_general` (and
  `isFinitePresentation_X_of_isStrictlyPerfect_general`), Stacks 0H98 on the opcycles;
* `Stacks.SheafOfModules.restrictOpcyclesAlongIsoGeneral`, restriction commutes with opcycles;
* `DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X_general` (in
  `Stacks.SheafOfModules`), the local core of the criterion.

The remaining inputs — the bounded-above local approximation
`AlgebraicGeometry.RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove_general`,
restriction along an arrow `Stacks.SheafOfModules.restrictComplexAlongGeneral`, flatness of the
terms of a strictly perfect complex and Stacks 08FD on a slice — are already universe-general.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion_general`.

## References

* [Stacks Project, Tag 08G7](https://stacks.math.columbia.edu/tag/08G7)
* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 0H98](https://stacks.math.columbia.edu/tag/0H98)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w d

/-! ### Truncations and opcycles at an arbitrary universe -/

section Auxiliary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

namespace SheafOfModules

variable {R}

/-- The canonical truncation in degrees `≥ r` has no terms below degree `r`. -/
theorem isZero_truncGE_X_general (P : CochainComplex (SheafOfModules.{w} R) ℤ) (r : ℤ) {i : ℤ}
    (hi : i < r) : IsZero ((P.truncGE r).X i) :=
  (P.truncGE r).isZero_of_isStrictlyGE r i hi

/-- The canonical truncation in degrees `≥ r` of a strictly perfect complex of `O`-modules is
strictly perfect, provided its degree-`r` opcycles are a direct summand of a finite free
`O`-module.

Above degree `r` the truncation agrees with `P`, in degree `r` it is the opcycles object — the
cokernel of `P^{r-1} ⟶ P^r` — and below `r` it vanishes; only the middle case needs the extra
hypothesis. This is the complex `E' ⟶ E^{a+1} ⟶ … ⟶ E^b` of the source's proof of Stacks 08G7,
with `r = a` and `E' = Coker(E^{a-1} ⟶ E^a)`. -/
theorem isStrictlyPerfect_truncGE_general {P : CochainComplex (SheafOfModules.{w} R) ℤ}
    (hP : IsStrictlyPerfect R P) (r : ℤ)
    (hop : IsDirectSummandOfFiniteFree R (P.opcycles r)) :
    IsStrictlyPerfect R (P.truncGE r) where
  bounded := by
    refine Set.Finite.subset (hP.bounded.union (Set.finite_singleton r)) ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi
    rcases lt_trichotomy i r with h | h | h
    · exact absurd (isZero_truncGE_X_general P r h) hi
    · exact Or.inr (by simp [h])
    · exact Or.inl fun hz => hi (hz.of_iso (P.truncGEXIso r i h))
  termDirectSummand i := by
    rcases lt_trichotomy i r with h | h | h
    · exact IsDirectSummandOfFiniteFree.of_isZero_general R (isZero_truncGE_X_general P r h)
    · subst h
      exact IsDirectSummandOfFiniteFree.of_iso R (P.truncGEXIsoOpcycles i) hop
    · exact IsDirectSummandOfFiniteFree.of_iso R (P.truncGEXIso r i h)
        (hP.termDirectSummand i)

end SheafOfModules

namespace Stacks.SheafOfModules

/-- **The brutal truncation of a strictly perfect complex is strictly perfect.** Each term of
`K.stupidTrunc e` is either the corresponding term of `K`, when its degree is in the image of
`e`, or a zero object; so the nonzero terms are among those of `K` and each term is a direct
summand of a finite free `O`-module.

With `e = ComplexShape.embeddingUpIntGE n` this is what lets a strictly perfect approximation be
replaced by one concentrated in degrees `≥ n` in the proof of Stacks 08G7. -/
theorem isStrictlyPerfect_stupidTrunc_general {ι : Type*} {c : ComplexShape ι}
    (e : c.Embedding (ComplexShape.up ℤ)) [e.IsRelIff]
    {P : CochainComplex (SheafOfModules.{w} R) ℤ} (hP : IsStrictlyPerfect R P) :
    IsStrictlyPerfect R (P.stupidTrunc e) where
  bounded := by
    refine hP.bounded.subset ?_
    intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    intro hz
    refine hi ?_
    by_cases h : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := h
      exact hz.of_iso (P.stupidTruncXIso e hj)
    · exact P.isZero_stupidTrunc_X e i (by simpa using h)
  termDirectSummand i := by
    by_cases h : ∃ j, e.f j = i
    · obtain ⟨j, hj⟩ := h
      exact IsDirectSummandOfFiniteFree.of_iso R (P.stupidTruncXIso e hj)
        (hP.termDirectSummand i)
    · exact IsDirectSummandOfFiniteFree.of_isZero_general R
        (P.isZero_stupidTrunc_X e i (by simpa using h))

end Stacks.SheafOfModules

end Auxiliary

namespace Stacks.SheafOfModules

variable (Y : RingedSite.{u, v, w})
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ T : Y.C, HasSheafify (Y.J.over T) AddCommGrpCat.{w}]
  [∀ T : Y.C, (Y.J.over T).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Every term of a strictly perfect complex of `O`-modules is of finite presentation**, being
a direct summand of a finite free `O`-module. -/
theorem isFinitePresentation_X_of_isStrictlyPerfect_general
    {P : CochainComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (i : ℤ) :
    (P.X i).IsFinitePresentation :=
  isFinitePresentation_of_isDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) _
    (hP.termDirectSummand i)

/-- **The degree-`a` opcycles of a strictly perfect complex of `O`-modules is of finite
presentation.** It is the cokernel of the differential `P^{a-1} ⟶ P^a`, whose source and target
are both of finite presentation, so Stacks 0H98 applies — it asks of the source only finite
type, which finite presentation implies. -/
theorem isFinitePresentation_opcycles_general
    {P : CochainComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) P) (a : ℤ) :
    (P.opcycles a).IsFinitePresentation := by
  have hprev : (ComplexShape.up ℤ).prev a = a - 1 := by rw [CochainComplex.prev]
  have _ : (P.X a).IsFinitePresentation :=
    isFinitePresentation_X_of_isStrictlyPerfect_general Y hP a
  have _ : (P.X (a - 1)).IsFinitePresentation :=
    isFinitePresentation_X_of_isStrictlyPerfect_general Y hP (a - 1)
  have _ : (cokernel (P.d (a - 1) a)).IsFinitePresentation :=
    LocalCokernel.isFinitePresentation_cokernel Y (P.d (a - 1) a)
  have e : cokernel (P.d (a - 1) a) ≅ P.opcycles a :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (P.d (a - 1) a))
      (P.opcyclesIsCokernel (a - 1) a hprev)
  exact (_root_.SheafOfModules.isFinitePresentation
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).prop_of_iso e inferInstance

end Stacks.SheafOfModules

section Restriction

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] generalPreservesFiniteColimitsOverMap preservesFiniteLimitsOverMapGeneral

/-- **An exact functor commutes with the opcycles of a complex**; here the comparison for
restriction along an arrow `g : V ⟶ U` of the site, with its source spelled as the opcycles of
the restricted complex rather than as the opcycles of a mapped short complex. -/
def restrictOpcyclesAlongIsoGeneral {U V : C} (g : V ⟶ U)
    (P : CochainComplex (_root_.SheafOfModules.{w} (R.over U)) ℤ) (k : ℤ) :
    (restrictComplexAlongGeneral R g P).opcycles k ≅
      (SheafOfModules.overMap.{w} R g).obj (P.opcycles k) :=
  ShortComplex.mapOpcyclesIso (P.sc k) (SheafOfModules.overMap.{w} R g)

end Stacks.SheafOfModules

end Restriction

namespace Stacks.SheafOfModules.DerivedTensorProduct

section Proof

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, u, u}}
  [HasSheafify Z.J AddCommGrpCat.{u}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{u}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Z) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor Z.O) (ComplexShape.up ℤ)]
  [∀ U : Z.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

variable
  [∀ U : Z.C, (Z.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : Z.C, (Z.J.over U).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  [∀ (U : Z.C) (W : Over U), HasWeakSheafify ((Z.J.over U).over W) AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (U : Z.C) (W : Over U),
    ((Z.J.over U).over W).HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]

/-- **The local core of Stacks 08G7, with the two concentration hypotheses on `P` given as the
vanishing of its terms** rather than as instances of `CochainComplex.IsStrictlyGE` and
`CochainComplex.IsStrictlyLE`.

This is `Stacks.SheafOfModules.DerivedTensorProduct.exists_iso_truncGE_and_isFlat_opcycles`;
typeclass synthesis does not cross between the two spellings of the structure sheaf of a slice,
so the two instance arguments are moved out of the instance context. -/
theorem exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X_general
    {Y : RingedSite.{u, u, u}} [HasSheafify Y.J AddCommGrpCat.{u}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} Y)]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) (ComplexShape.up ℤ)]
    (T : DerivedTensorProduct.{u, u, u, d} Y)
    (E : RingedSite.DerivedModules.{u, u, u, d} Y) (n b : ℤ)
    (Ecpx : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ)
    (eE : DerivedCategory.Q.obj Ecpx ≅ E)
    (P : CochainComplex (RingedSite.Modules.{u, u, u} Y) ℤ)
    (hGE : ∀ i : ℤ, i < n → IsZero (P.X i)) (hLE : ∀ i : ℤ, b < i → IsZero (P.X i))
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.X i))
    (α : P ⟶ Ecpx)
    (hα : ∀ i : ℤ, n + 1 ≤ i → IsIso (HomologicalComplex.homologyMap α i))
    (hamp : HasTorAmplitude T E (n + 1) b) :
    Nonempty (DerivedCategory.Q.obj (P.truncGE (n + 1)) ≅ E) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O) (P.opcycles (n + 1)) := by
  have hge : CochainComplex.IsStrictlyGE P n := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => hGE i hi
  have hle : CochainComplex.IsStrictlyLE P b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => hLE i hi
  exact exists_iso_truncGE_and_isFlat_opcycles T E n b Ecpx eE P hflat α hα hamp

attribute [local instance] AlgebraicGeometry.RingedSite.overMapLimits
  AlgebraicGeometry.RingedSite.overMapColimits

/-- **Stacks 08G7 on the diagonal.** Let `(C, O)` be a ringed site and let `T` be a derived
tensor product on `D(O)`. An object of `D(O)` with Tor amplitude in `[a, b]` for `T`, with
`a ≤ b`, which is `(a - 1)`-pseudo-coherent, is perfect.

The proof reads Tor amplitude on each slice `(C/U, O|_U)`, which needs a derived tensor product
there; that is the derived tensor product of Stacks 06YU,
`Stacks.SheafOfModules.canonicalDerivedTensorProduct`, which exists on each slice under the
hypotheses already in force, so it is not a parameter of the statement. -/
theorem torAmplitudePerfectnessCriterion_general
    (T : DerivedTensorProduct.{u, u, u, d} Z) (E : RingedSite.DerivedModules.{u, u, u, d} Z)
    (a b : ℤ) (hab : a ≤ b) (hamp : HasTorAmplitude T E a b)
    (hpc : Z.IsPseudoCoherentFrom E (a - 1)) :
    Z.IsPerfect E := by
  classical
  let T' : ∀ U : Z.C, DerivedTensorProduct.{u, u, u, d} (Z.over U) := fun U =>
    _root_.Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u, u, d} (Z.over U)
  have hzero : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} Z) i).obj E) :=
    (DerivedCategory.isLE_iff E b).1 (isLE_of_hasTorAmplitude T E hamp)
  obtain ⟨Ecpx, ⟨eE⟩, hloc⟩ :=
    RingedSite.exists_local_strictlyPerfect_approximation_boundedAbove_general Z E (a - 1) b
      (by omega) hpc hzero
  -- The comparison of the derived restriction of `E` with the restriction of `Ecpx`.
  have hrepr : ∀ V : Z.C, DerivedCategory.Q.obj (Z.restrictComplex Ecpx V) ≅
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategoryFactors.app Ecpx).symm ≪≫
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).mapDerivedCategory.mapIso eE
  -- The local core of the criterion, for a complex `Q` on a slice resolving `E` in degrees `≥ a`.
  have core : ∀ (W : Z.C) (Q : CochainComplex (RingedSite.Modules.{u, u, u} (Z.over W)) ℤ),
      IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W) Q →
      (∀ i : ℤ, i < a - 1 → IsZero (Q.X i)) → (∀ i : ℤ, b < i → IsZero (Q.X i)) →
      ∀ α : Q ⟶ Z.restrictComplex Ecpx W,
      (∀ i : ℤ, a - 1 + 1 ≤ i → IsIso (HomologicalComplex.homologyMap α i)) →
      Nonempty (DerivedCategory.Q.obj (Q.truncGE a) ≅
        (RingedSite.derivedRestriction.{u, u, u, d} Z W).obj E) ∧
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (Z.over W).O) (Q.opcycles a) := by
    intro W Q hQ hGE hLE α hα
    have hampW : HasTorAmplitude (T' W)
        ((RingedSite.derivedRestriction.{u, u, u, d} Z W).obj E) (a - 1 + 1) b := by
      rw [show a - 1 + 1 = a from by omega]
      exact hasTorAmplitude_derivedRestriction T W (T' W) E a b hab hamp
    have h := exists_iso_truncGE_and_isFlat_opcycles_of_isZero_X_general (Y := Z.over W) (T' W)
      ((RingedSite.derivedRestriction.{u, u, u, d} Z W).obj E) (a - 1) b
      (Z.restrictComplex Ecpx W) (hrepr W) Q hGE hLE
      (fun i => isFlat_X_of_isStrictlyPerfect (Y := Z.over W) hQ i) α hα hampW
    rwa [show a - 1 + 1 = a from by omega] at h
  refine RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect Z E (fun U => ?_)
  obtain ⟨S₀, hS₀, hprop⟩ := hloc U
  have key : ∀ (V : Z.C) (f : V ⟶ U), S₀ f → ∃ Sv : Sieve V, Sv ∈ Z.J V ∧
      ∀ ⦃W : Z.C⦄ (k : W ⟶ V), Sv k →
        ∃ Q : CochainComplex
            (_root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W) Q ∧
          Nonempty (DerivedCategory.Q.obj Q ≅
            (SheafOfModules.overFunctor.{u}
              (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) W).mapDerivedCategory.obj E) := by
    intro V f hf
    obtain ⟨P, hP, hPzero, α, hαiso, hαepi⟩ := hprop f hf
    have hPLE : CochainComplex.IsStrictlyLE P b := by
      rw [CochainComplex.isStrictlyLE_iff]
      exact fun i hi => hPzero i hi
    have hPgGE : CochainComplex.IsStrictlyGE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) := inferInstance
    have hPgLE : CochainComplex.IsStrictlyLE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) b := inferInstance
    have hPg : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V)
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) :=
      isStrictlyPerfect_stupidTrunc_general
        ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V) _ hP
    have hαg : ∀ i : ℤ, a - 1 + 1 ≤ i → IsIso (HomologicalComplex.homologyMap
        (HomologicalComplex.ιStupidTrunc P
          (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α) i) := by
      intro i hi
      rw [HomologicalComplex.homologyMap_comp]
      have h1 := StacksDraft.StupidTruncation.isIso_homologyMap_ιStupidTruncGE P (a - 1) i
        (by omega)
      have h2 := hαiso i (by omega)
      infer_instance
    have hop := (core V _ hPg
      (fun i hi => CochainComplex.isZero_of_isStrictlyGE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) i hi)
      (fun i hi => CochainComplex.isZero_of_isStrictlyLE
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) b i hi) _ hαg).2
    have hfpop :
        ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).opcycles a).IsFinitePresentation :=
      isFinitePresentation_opcycles_general (Z.over V) hPg a
    obtain ⟨Sv', hSv', hsummand⟩ :=
      exists_coveringSieve_isDirectSummandOfFiniteFree_overMap_of_isFinitePresentation V Z.O
        ((P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))).opcycles a) hfpop hop
        (Over.mk (𝟙 V))
    refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) Sv', (Z.J.mem_over_iff Sv').1 hSv', ?_⟩
    intro W k hk
    rw [Sieve.overEquiv_iff] at hk
    have hsum := hsummand _ hk
    simp only [Over.mk_left, Over.mk_hom, Category.comp_id] at hsum
    have hPr : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
        (restrictComplexAlongGeneral (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))) :=
      isStrictlyPerfect_restrictComplexAlong_general
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k hPg
    have hPrGE : ∀ i : ℤ, i < a - 1 → IsZero ((restrictComplexAlongGeneral
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).X i) :=
      fun i hi => (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) (a - 1) i hi)
    have hPrLE : ∀ i : ℤ, b < i → IsZero ((restrictComplexAlongGeneral
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).X i) :=
      fun i hi => (SheafOfModules.overMap.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k).map_isZero
        (CochainComplex.isZero_of_isStrictlyLE
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) b i hi)
    have hopr : IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
        ((restrictComplexAlongGeneral (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).opcycles a) :=
      IsDirectSummandOfFiniteFree.of_iso _ (restrictOpcyclesAlongIsoGeneral
        (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
        (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1))) a) hsum
    have hQ : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over W)
        ((restrictComplexAlongGeneral (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k
          (P.stupidTrunc (ComplexShape.embeddingUpIntGE (a - 1)))).truncGE a) :=
      _root_.SheafOfModules.isStrictlyPerfect_truncGE_general hPr a hopr
    have hαr : ∀ i : ℤ, a - 1 + 1 ≤ i → IsIso (HomologicalComplex.homologyMap
        (((SheafOfModules.overMap.{u}
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k).mapHomologicalComplex
            (ComplexShape.up ℤ)).map (HomologicalComplex.ιStupidTrunc P
              (ComplexShape.embeddingUpIntGE (a - 1)) ≫ α) ≫
          (restrictComplexAlongOverIsoGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k Ecpx).hom) i) := by
      intro i hi
      rw [HomologicalComplex.homologyMap_comp]
      refine IsIso.comp_isIso'
        (AlgebraicGeometry.RingedSpace.isIso_homologyMap_map _ _ i (hαg i hi)) ?_
      exact (HomologicalComplex.homologyMapIso
        (restrictComplexAlongOverIsoGeneral
          (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) k Ecpx) i).isIso_hom
    obtain ⟨iso⟩ := (core W _ hPr hPrGE hPrLE _ hαr).1
    exact ⟨_, hQ, ⟨iso⟩⟩
  choose Sv hSv hmodel using key
  have hbind : Sieve.bind S₀ (fun {Y} {f} hf => Sv Y f hf) ∈ Z.J U := by
    refine Z.J.transitive hS₀ _ fun V f hf => ?_
    obtain ⟨W, k, s, hs, hfac⟩ := hf
    refine Z.J.superset_covering (fun Y g hg => ?_)
      (Z.J.pullback_stable k (hSv _ s hs))
    exact ⟨W, g ≫ k, s, hs, hg, by simp [hfac, Category.assoc]⟩
  refine ⟨(Sieve.bind S₀ (fun {Y} {f} hf => Sv Y f hf)).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact hbind
  intro V g hg
  obtain ⟨W, k, s, hs, hk, _⟩ :=
    (show Sieve.bind S₀ (fun {Y} {f} hf => Sv Y f hf) g from hg)
  exact hmodel _ s hs k hk

end Proof

end Stacks.SheafOfModules.DerivedTensorProduct

end
