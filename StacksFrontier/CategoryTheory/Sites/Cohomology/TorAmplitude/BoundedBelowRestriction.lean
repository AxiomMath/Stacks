module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.RestrictionToSlice
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowFlatRepresentative
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Restriction

/-!
# Tor amplitude in `[a, ∞)` is inherited by the restriction to a slice

Let `(C, O)` be a ringed site, let `U` be an object of `C` and let `E` be an object of `D(O)` of
Tor amplitude in `[a, ∞)`. Then the restriction of `E` to the localized ringed site
`(C/U, O|_U)` again has Tor amplitude in `[a, ∞)`.

`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction` is the same
statement for a bounded interval `[a, b]`, and the half-infinite case does not follow from it:
Tor amplitude in `[a, ∞)` bounds nothing above, so there is no interval to carry across.

## Main results

* `DerivedTensorProduct.exists_kFlatRepresentative_restriction_of_hasTorAmplitudeGE`: an object
  of Tor amplitude in `[a, ∞)` is represented by a complex of flat `O`-modules which vanishes
  below `a`, is K-flat, and stays K-flat on every slice. This is Tag 0F1M, i.e.
  `Stacks.SheafOfModules.DerivedTensorProduct.exists_kFlatRepresentative_of_hasTorAmplitudeGE`,
  with the extra clause.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_derivedRestriction`: **Tor
  amplitude in `[a, ∞)` restricts to a slice**, for *any* derived tensor product on the slice.

## Why the bounded proof does not transcribe

The bounded statement goes through Tag 08G1: it represents `E` by a complex of flat modules
concentrated in `[a, b]`, restricts it — flatness survives by Tag 0E8J, the concentration
survives because restriction is additive — and reads Tag 08G1 back on the slice. The restricted
complex is K-flat there for free, being bounded above with flat terms (Tag 06YQ).

With only a lower bound that last step is gone, and K-flatness is *not* a property that
transports along a functor: it quantifies over the acyclic complexes of the site, and the
acyclic complexes of `C/U` are not the restrictions of those of `C`. This is recorded in the
module documentation of
`StacksFrontier/CategoryTheory/Sites/Cohomology/KFlat/RestrictionToSlice.lean`, which also supplies
what is needed instead:
`Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall` produces
*one* K-flat resolution with flat terms whose restriction to **every** slice is again K-flat,
because the colimit presentation of Tag 06YS it is built from restricts clause by clause.

The representative of Tag 0F1M is the truncation `τ_{≥a}A` of such a resolution `A`, and the
argument making it K-flat restricts along with the resolution. Writing `S` for the kernel
sequence of `A ⟶ τ_{≥a}A`:

* the terms of `τ_{≥a}A` are flat — in degrees above `a` they are those of `A`, in degree `a`
  the cokernel of `d_A^{a-1}`, flat by the Tor bound (Tag 08G0, in the form
  `isFlat_cokernel_of_hasTorAmplitudeGE`) — hence so are their restrictions, by Tag 0E8J;
* `S.X₁` is concentrated in degrees `≤ a` with flat terms, hence so is its restriction, which is
  therefore K-flat by Tag 06YQ on the slice;
* the restriction of `A` is K-flat by the resolution's own clause;
* so the restriction of `τ_{≥a}A` is K-flat by two-out-of-three for K-flatness in a short exact
  sequence with flat terms on the right, restriction being exact.

The Tor bound on the slice then follows from the easy direction of Tag 0F1M, which needs nothing
but K-flatness and the vanishing, and in particular no comparison of the two derived tensor
products: the tensor product on the slice is arbitrary, exactly as in the bounded statement and
in `Stacks.SheafOfModules.DerivedTensorProduct.LocallyHasFiniteTorDimension`.

## Implementation notes

The steps above are stated as separate private lemmas, each in the smallest instance context it
needs, rather than as `have`s inside one proof. They are not independently interesting: the
reason is the elaboration cost. The sheaf-of-modules instance context of a ringed site together
with the one of all of its slices is large enough that a single declaration carrying both
exceeds the default heartbeat budget on the restricted short exact sequence alone, and raising
that budget is not an option in this library. Splitting gives each step its own budget and keeps
the slice instances out of the four steps that are about the site itself.

The three steps about the site repeat steps of the proof of
`Stacks.SheafOfModules.DerivedTensorProduct.exists_kFlatRepresentative_of_hasTorAmplitudeGE`.
They are repeated rather than reused because that statement records only that a representative
exists, not which complex it is, and the clause added here is about that complex.

## References

* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
* [Stacks Project, Tag 0E8J](https://stacks.math.columbia.edu/tag/0E8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

/-! ### The truncation of a K-flat resolution, on the site itself -/

section Site

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The kernel sequence of the projection onto a truncation is short exact.** The projection is
an epimorphism, being one in each degree. -/
private theorem shortExact_kernelSequence_πTruncGE
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ) :
    (ShortComplex.kernelSequence (A.πTruncGE a)).ShortExact := by
  have hπepi : Epi (A.πTruncGE a) :=
    HomologicalComplex.epi_of_epi_f _ fun i => by
      dsimp only [CochainComplex.πTruncGE]
      infer_instance
  exact ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance hπepi

/-- **The kernel of the projection onto `τ_{≥a}` vanishes above `a`**, because the projection is
an isomorphism in each degree above `a`. -/
private theorem isStrictlyLE_kernelSequence_πTruncGE
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ) :
    (ShortComplex.kernelSequence (A.πTruncGE a)).X₁.IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have _ : IsIso ((A.πTruncGE a).f i) :=
    A.isIso_πTruncGE_f _
      (show (ComplexShape.embeddingUpIntGE a).f (i - a).natAbs = i by
        rw [ComplexShape.embeddingUpIntGE_f, Int.natAbs_of_nonneg (by omega)]
        omega)
      (by rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]; omega)
  have hSi := (shortExact_kernelSequence_πTruncGE A a).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)
  have _ := hSi.mono_f
  refine IsZero.of_mono_eq_zero _ (hSi.exact.mono_g_iff.1 ?_)
  exact inferInstanceAs (Mono ((A.πTruncGE a).f i))

/-- **The kernel of the projection onto `τ_{≥a}` has flat terms**, by two-out-of-three for
flatness in the degreewise short exact sequence. -/
private theorem isFlat_kernelSequence_πTruncGE_X
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ)
    (hAflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (A.X i))
    (hTruncFlat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) ((A.truncGE a).X i)) :
    ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((ShortComplex.kernelSequence (A.πTruncGE a)).X₁.X i) := fun i =>
  Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact X.O
    ((ShortComplex.kernelSequence (A.πTruncGE a)).map
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
    ((shortExact_kernelSequence_πTruncGE A a).map_of_exact
      (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
    (hAflat i) (hTruncFlat i)

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- **The terms of `τ_{≥a}A` are flat**, for `A` a K-flat complex of flat modules whose class has
Tor amplitude in `[a, ∞)`. Above `a` they are the terms of `A`; in degree `a` the term is the
cokernel of `d_A^{a-1}`, flat by Tag 08G0 in the form
`isFlat_cokernel_of_hasTorAmplitudeGE`; below `a` the term is zero. -/
private theorem isFlat_truncGE_X_of_hasTorAmplitudeGE (T : DerivedTensorProduct.{u, u, u, d} X)
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ)
    (hAkflat : IsKFlat X.O A)
    (hAflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (A.X i))
    (hAamp : HasTorAmplitudeGE T (DerivedCategory.Q.obj A) a) :
    ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((A.truncGE a).X i) := by
  have hCoker := isFlat_cokernel_of_hasTorAmplitudeGE T A a hAkflat hAflat hAamp
  have eOpCoker : A.opcycles a ≅
      (cokernel (A.d (a - 1) a) : RingedSite.Modules.{u, u, u} X) :=
    IsColimit.coconePointUniqueUpToIso
      (A.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
  intro i
  rcases lt_trichotomy i a with hlt | heq | hgt
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero X.O
      ((A.truncGE a).isZero_of_isStrictlyGE a i hlt)
  · rw [heq]
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O
      (eOpCoker.symm ≪≫ (A.truncGEXIsoOpcycles a).symm) hCoker
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O
      (A.truncGEXIso a i hgt).symm (hAflat i)

end Site

/-! ### Restriction to a slice -/

section Slice

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- **Restriction to a slice is exact**, by Tag 04IX: it carries a short exact sequence of
sheaves of `O`-modules to one of sheaves of `O|_U`-modules. The two preservation facts are taken
by name rather than by instance search, as in
`Stacks.SheafOfModules.GoodExtensionByZero.restrict_shortExact`. -/
private theorem shortExact_map_over (U : X.C)
    {S : ShortComplex (RingedSite.Modules.{u, u, u} X)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)).ShortExact := by
  have hl := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  have hc := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) U
  exact hS.map_of_exact (SheafOfModules.overFunctor.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U)

/-- The restriction of a short exact sequence of complexes is a monomorphism in each degree,
hence a monomorphism. -/
private theorem mono_map_restrictComplex_f (U : X.C)
    {S : ShortComplex (CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)} (hS : S.ShortExact) :
    Mono (S.map ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ))).f :=
  HomologicalComplex.mono_of_mono_f _ fun i =>
    (shortExact_map_over U
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))).mono_f

/-- The restriction of a short exact sequence of complexes is an epimorphism in each degree,
hence an epimorphism. -/
private theorem epi_map_restrictComplex_g (U : X.C)
    {S : ShortComplex (CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)} (hS : S.ShortExact) :
    Epi (S.map ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ))).g :=
  HomologicalComplex.epi_of_epi_f _ fun i =>
    (shortExact_map_over U
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))).epi_g

/-- The restriction of a short exact sequence of complexes is exact in each degree, hence
exact. -/
private theorem exact_map_restrictComplex (U : X.C)
    {S : ShortComplex (CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)} (hS : S.ShortExact) :
    (S.map ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ))).Exact :=
  HomologicalComplex.exact_of_degreewise_exact _ fun i =>
    (shortExact_map_over U
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))).exact

/-- **Restriction to a slice carries a short exact sequence of complexes to one**, restriction
being exact degreewise by Tag 04IX and monomorphy, epimorphy and exactness of a short complex of
complexes all being degreewise conditions.

The three clauses are separate declarations above, and the preservation facts inside them are
taken by name rather than by instance search: a single declaration applying exactness to the
functor on complexes in one step exhausts the heartbeat budget. -/
private theorem shortExact_map_restrictComplex (U : X.C)
    {S : ShortComplex (CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ)} (hS : S.ShortExact) :
    (S.map ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
      (ComplexShape.up ℤ))).ShortExact where
  mono_f := mono_map_restrictComplex_f U hS
  epi_g := epi_map_restrictComplex_g U hS
  exact := exact_map_restrictComplex U hS

/-- **The restriction of the kernel of `A ⟶ τ_{≥a}A` to a slice is K-flat**: it is concentrated
in degrees `≤ a` with flat terms, both conditions surviving restriction, so Tag 06YQ applies on
the slice. -/
private theorem isKFlat_restrictComplex_kernelSequence (U : X.C)
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ)
    (hAflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (A.X i))
    (hTruncFlat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) ((A.truncGE a).X i)) :
    IsKFlat (X.over U).O
      (X.restrictComplex (ShortComplex.kernelSequence (A.πTruncGE a)).X₁ U) :=
  Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat (X.over U).O _
    ⟨a, (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi =>
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero
        (((CochainComplex.isStrictlyLE_iff _ _).1
          (isStrictlyLE_kernelSequence_πTruncGE A a)) i hi)⟩
    fun i => Stacks.SheafOfModules.FlatRestriction.isFlat_over X U _
      (isFlat_kernelSequence_πTruncGE_X A a hAflat hTruncFlat i)

/-- The two restricted maps of the kernel sequence of `A ⟶ τ_{≥a}A` compose to zero. -/
private theorem restrictComplexMap_kernelSequence_comp_zero (U : X.C)
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ) :
    ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (ShortComplex.kernelSequence (A.πTruncGE a)).f ≫
        ((SheafOfModules.overFunctor.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (ShortComplex.kernelSequence (A.πTruncGE a)).g = 0 := by
  rw [← Functor.map_comp, (ShortComplex.kernelSequence (A.πTruncGE a)).zero, Functor.map_zero]

/-- **The restricted kernel sequence of `A ⟶ τ_{≥a}A`, written out**, is short exact. Writing the
three terms out rather than as the image of the sequence on `X` is what makes the two-out-of-three
step below affordable: its three terms are then syntactically the restrictions of the kernel, of
`A` and of `τ_{≥a}A`, so nothing has to be reduced to recognise them. -/
private theorem shortExact_restrictKernelSequence (U : X.C)
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ) :
    (ShortComplex.mk
      (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (ShortComplex.kernelSequence (A.πTruncGE a)).f)
      (((SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (ShortComplex.kernelSequence (A.πTruncGE a)).g)
      (restrictComplexMap_kernelSequence_comp_zero U A a)).ShortExact := by
  exact shortExact_map_restrictComplex U (shortExact_kernelSequence_πTruncGE A a)

/-- **The restriction of `τ_{≥a}A` to a slice is K-flat**, for `A` a complex of flat modules
whose restriction to that slice is K-flat and whose truncation has flat terms: the restricted
kernel sequence is short exact with K-flat first and second terms and flat terms on the right,
so two-out-of-three for K-flatness applies on the slice. -/
private theorem isKFlat_restrictComplex_truncGE (U : X.C)
    (A : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ)
    (hAflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (A.X i))
    (hArestr : IsKFlat (X.over U).O (X.restrictComplex A U))
    (hTruncFlat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) ((A.truncGE a).X i)) :
    IsKFlat (X.over U).O (X.restrictComplex (A.truncGE a) U) :=
  Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact (X.over U).O
    (ShortComplex.mk _ _ (restrictComplexMap_kernelSequence_comp_zero U A a))
    (shortExact_restrictKernelSequence U A a)
    (fun i => Stacks.SheafOfModules.FlatRestriction.isFlat_over X U _ (hTruncFlat i))
    (isKFlat_restrictComplex_kernelSequence U A a hAflat hTruncFlat) hArestr

variable [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ U : X.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Tag 0F1M with a clause for the slices.** An object of `D(O)` of Tor amplitude in `[a, ∞)`
is represented by a K-flat complex of flat `O`-modules vanishing in every degree below `a` whose
restriction to every slice `C/U` is again K-flat.

The complex is the truncation `τ_{≥a}A` of a K-flat resolution `A` with flat terms chosen so
that its restriction to every slice is K-flat, which
`Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall` supplies; the
module documentation explains why the resolution has to be chosen before the truncation is
taken. -/
theorem exists_kFlatRepresentative_restriction_of_hasTorAmplitudeGE
    (T : DerivedTensorProduct.{u, u, u, d} X)
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) (hE : HasTorAmplitudeGE T E a) :
    ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
      IsKFlat X.O K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
      (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
      (∀ U : X.C, IsKFlat (X.over U).O (X.restrictComplex K U)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨A, p, hAkflat, hAflat, hp, -, hArestr⟩ :=
    Stacks.SheafOfModules.KFlatRestriction.exists_kFlatResolution_restriction_forall X.O
      (DerivedCategory.Q.objPreimage E)
  have _ : QuasiIso p := hp
  have eA : DerivedCategory.Q.obj A ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hAamp : HasTorAmplitudeGE T (DerivedCategory.Q.obj A) a := hE.of_iso eA
  have hAGE : A.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff, DerivedCategory.isGE_iff]
    exact fun i hi => isZero_homology_of_hasTorAmplitudeGE T _ a hAamp i hi
  have _ : A.IsGE a := hAGE
  have hTruncFlat := isFlat_truncGE_X_of_hasTorAmplitudeGE T A a hAkflat hAflat hAamp
  have hKerFlat := isFlat_kernelSequence_πTruncGE_X A a hAflat hTruncFlat
  have hKerKFlat : IsKFlat X.O (ShortComplex.kernelSequence (A.πTruncGE a)).X₁ :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O _
      ⟨a, isStrictlyLE_kernelSequence_πTruncGE A a⟩ hKerFlat
  refine ⟨A.truncGE a,
    Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact X.O
      (ShortComplex.kernelSequence (A.πTruncGE a))
      (shortExact_kernelSequence_πTruncGE A a) hTruncFlat hKerKFlat hAkflat,
    hTruncFlat, fun i hi => (A.truncGE a).isZero_of_isStrictlyGE a i hi,
    fun U => isKFlat_restrictComplex_truncGE U A a hAflat (hArestr U) hTruncFlat,
    ⟨(asIso (DerivedCategory.Q.map (A.πTruncGE a))).symm ≪≫ eA⟩⟩

/-- **Tor amplitude in `[a, ∞)` restricts to a slice.** If an object `E` of `D(O)` has Tor
amplitude in `[a, ∞)` for a derived tensor product `T` on `D(O)`, then its restriction to the
ringed site localized at an object `U` has Tor amplitude in `[a, ∞)` for *any* derived tensor
product `T'` on that slice.

This is the half-infinite counterpart of
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_derivedRestriction`, and it is what
a local argument about a complex with no upper Tor bound begins with. -/
theorem hasTorAmplitudeGE_derivedRestriction (T : DerivedTensorProduct.{u, u, u, d} X) (U : X.C)
    (T' : DerivedTensorProduct.{u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) (hamp : HasTorAmplitudeGE T E a) :
    HasTorAmplitudeGE T' ((RingedSite.derivedRestriction.{u, u, u, d} X U).obj E) a := by
  obtain ⟨K, -, -, hzero, hrestr, ⟨e⟩⟩ :=
    exists_kFlatRepresentative_restriction_of_hasTorAmplitudeGE T E a hamp
  let KU : CochainComplex (RingedSite.Modules.{u, u, u} (X.over U)) ℤ := X.restrictComplex K U
  refine hasTorAmplitudeGE_of_kFlatRepresentative T' _ a KU (hrestr U) (fun i hi => ?_) ?_
  · exact (SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).map_isZero (hzero i hi)
  · exact ((SheafOfModules.overFunctor.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).mapDerivedCategory.mapIso e

end Slice

end Stacks.SheafOfModules.DerivedTensorProduct

end
