module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.SliceApproximationBridge
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.DistinguishedTriangles
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of the summands of a pseudo-coherent biproduct

Let `(C, O)` be a ringed site and `m : ℤ`. If `K ⊞ L` is `m`-pseudo-coherent in `D(O)`, then so
are `K` and `L`; the same holds for pseudo-coherence without a fixed degree. This is Stacks
08FW.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_left_of_biprod_general` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_right_of_biprod_general`: the two
  assertions at a fixed degree, with the objects of the site, its morphisms and the sections
  of the structure sheaf at independent universes.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_left_of_biprod_general` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherent_right_of_biprod_general`: the same without a
  fixed degree.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_left_of_biprod` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_right_of_biprod`: the two assertions at a
  fixed degree.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_left_of_biprod` and
  `AlgebraicGeometry.RingedSite.isPseudoCoherent_right_of_biprod`: the two assertions without
  a fixed degree.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_distinguished_general`: **Stacks 08FV**
  without a fixed degree, in all three positions of a distinguished triangle, which the
  degree-free criterion `isPseudoCoherent_iff_forall` reduces to the three parts of the source.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isZero_general`: a zero object of `D(O)` is
  pseudo-coherent.

Four utilities proved on the way are stated for use elsewhere, since the descending induction
on pseudo-coherence in the proof of the first assertion of [Stacks, Tag 0FPV] is built out of
exactly them:

* `AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom`:
  Stacks 08FU (2), the degree-free criterion — the induction's exit.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isLE_sub_one`: an object of
  `D^{≤ t - 1}(O)` is `t`-pseudo-coherent — the induction's entry.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_mono_general`, of
  `StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/SliceApproximationBridge.lean`:
  `n`-pseudo-coherence weakens to every degree `≥ n`, which is what lets one step of the
  induction feed the next.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_isStrictlyPerfect_approximation`: a
  strictly perfect complex with a morphism to an object of `D(O)` which is invertible on
  cohomology above `n` and epic in degree `n` makes that object `n`-pseudo-coherent — what each
  step of the induction produces, and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_forall_isZero_homology` is the case of
  the zero complex.

## Implementation notes

The source reduces to the bounded case on a covering and then descends through the
distinguished triangles `(L⟦n⟧, L⟦n⟧ ⊞ L⟦n-1⟧, L⟦n-1⟧)`. The formalization below follows the
same shape, with the descent isolated as `summands_of_biprod_step`: for a predicate `P n A` on
`D(O)` which is isomorphism-invariant, monotone in `n`, and stable in the sense of Stacks
08FV (1) applied to the split triangle `(A, A ⊞ B, B)`, knowledge of `P N A` and `P N B` for
one `N ≥ n` together with `P n (A ⊞ B)` gives `P n A` and `P n B`, by downward induction on the
degree.

Three ingredients make that applicable.

* Over an object `V` of the site carrying a strictly perfect approximation of `(A ⊞ B)|_V`, the
  cohomology of both `A|_V` and `B|_V` vanishes above the (finite) support of the
  approximation, since each is a retract of `A ⊞ B` and the approximation is invertible on
  cohomology in high degrees. A derived object with vanishing cohomology from a degree on is
  pseudo-coherent from that degree on, approximated by the zero complex
  (`isPseudoCoherentFrom_of_homology_isZero`). This supplies the `N` above.
* Pseudo-coherence transfers along a map which is invertible on cohomology above `m` and epic
  in degree `m` (`isPseudoCoherentFrom_of_homologyMap`); combined with the stupid truncation of
  a strictly perfect complex, which is again strictly perfect, this turns a strictly perfect
  approximation of a *complex* into pseudo-coherence of the corresponding *derived object*
  (`isPseudoCoherentFrom_of_strictlyPerfect_approximation`).
* The conclusion so obtained is local on the site, and Stacks 08FU (3),
  `isPseudoCoherentFrom_of_locally`, assembles it.

## References

* [Stacks Project, Tag 08FW](https://stacks.math.columbia.edu/tag/08FW)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

universe u v w d d'

namespace AlgebraicGeometry.RingedSite

section Descent

/-- Downward induction through the split triangles `(A, A ⊞ B, B)`. For a degree-indexed
predicate `P` on a preadditive category with binary biproducts which is isomorphism-invariant,
monotone in the degree, and such that `P (n + 1) A` and `P n (A ⊞ B)` give `P n B`: if `A` and
`B` both satisfy `P` in some degree `N ≥ n` and `A ⊞ B` satisfies `P` in degree `n`, then both
`A` and `B` satisfy `P` in degree `n`. -/
private theorem summands_of_biprod_step
    {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
    (P : ℤ → C → Prop)
    (hiso : ∀ n {A B}, (A ≅ B) → P n A → P n B)
    (hmono : ∀ {n i}, n ≤ i → ∀ A, P n A → P i A)
    (hstep : ∀ n A B, P (n + 1) A → P n (A ⊞ B) → P n B)
    (A B : C) (n N : ℤ) (hnN : n ≤ N)
    (hA : P N A) (hB : P N B) (hAB : P n (A ⊞ B)) :
    P n A ∧ P n B := by
  have descend : ∀ i : ℤ, i ≤ N → n ≤ i → P i A ∧ P i B :=
    Int.leInductionDown (m := N) (fun _ => ⟨hA, hB⟩)
      (fun i _ ih hni => by
        have hi := ih (by omega)
        have hsum := hmono hni (A ⊞ B) hAB
        have hA' : P (i - 1 + 1) A := by simpa only [sub_add_cancel] using hi.1
        have hB' : P (i - 1 + 1) B := by simpa only [sub_add_cancel] using hi.2
        exact ⟨hstep (i - 1) B A hB' (hiso _ (biprod.braiding A B) hsum),
          hstep (i - 1) A B hA' hsum⟩)
  exact descend n hnN le_rfl

/-- A functor to a category with zero morphisms sends a retract of an object with zero image to
an object with zero image. -/
private theorem isZero_map_of_retract
    {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms D]
    (F : C ⥤ D) {K L : C} (i : K ⟶ L) (r : L ⟶ K)
    (hir : i ≫ r = 𝟙 K) (hL : IsZero (F.obj L)) : IsZero (F.obj K) := by
  rw [IsZero.iff_id_eq_zero, ← F.map_id, ← hir, F.map_comp,
    hL.eq_of_src (F.map r) 0, comp_zero]

end Descent

section StrictlyPerfectSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- A zero sheaf of modules is a direct summand of the free module on the empty index type. -/
private theorem isDirectSummandOfFiniteFree_of_isZero (M : SheafOfModules.{w} R)
    (hM : IsZero M) : IsDirectSummandOfFiniteFree R M :=
  (isDirectSummandOfFiniteFree_iff_free R M).mpr ⟨0, 0, 0, hM.eq_of_src _ _⟩

/-- Restriction to a slice of the site carries a strictly perfect complex to a strictly
perfect complex. -/
private theorem isStrictlyPerfect_over {U : C}
    [HasSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {P : CochainComplex (SheafOfModules.{w} R) ℤ} (hP : IsStrictlyPerfect R P) :
    IsStrictlyPerfect (R.over U)
      (((SheafOfModules.overFunctor.{w} R U).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  have : PreservesFiniteColimits (SheafOfModules.overFunctor.{w} R U) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.overFunctorUnitIso R U) hP

end StrictlyPerfectSite

section Main

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective iterHasSheafify iterWEq
  iterHasSheafifyAll iterWEqAll ovFunctorLimits ovFunctorLimitsAll ovFunctorColimits
  ovFunctorColimitsAll

/-- Restriction of sheaves of `O`-modules to the slice over `U` preserves homology. -/
local instance ovFunctorHomology (U : X.C) :
    (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- Restriction of sheaves of `O`-modules to the slice over any `U` preserves finite limits. -/
local instance ovFunctorLimitsAllBase :
    ∀ U : X.C,
      PreservesFiniteLimits
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  fun U => Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of `O`-modules to the slice over any `U` is an additive functor. -/
local instance ovFunctorAdditiveAllBase :
    ∀ U : X.C,
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U).Additive :=
  fun _ => inferInstance

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

omit hDer in
/-- An object of `D(O)` is pseudo-coherent exactly when it is `n`-pseudo-coherent for every
`n`. The content is the forward direction of Stacks 08FU (2): a single complex representing
the object is `n`-pseudo-coherent for every `n` at once. -/
private theorem isPseudoCoherent_iff_forall
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    X.IsPseudoCoherent E ↔ ∀ n, X.IsPseudoCoherentFrom E n := by
  constructor
  · rintro ⟨P, hP, e⟩ n
    exact ⟨P, hP n, e⟩
  · intro h
    obtain ⟨P, _, ⟨e⟩⟩ := h 0
    exact ⟨P, fun n => isPseudoCoherentComplexFrom_of_iso_general X E n (h n) P e, ⟨e⟩⟩

omit [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  hDer in
/-- Pseudo-coherence of complexes transfers along a map which is invertible on cohomology
above `n` and epic on cohomology in degree `n`: restriction to a slice is exact, so it
preserves both conditions, and the approximations compose. -/
private theorem isPseudoCoherentComplexFrom_of_homologyMap
    (A B : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (n : ℤ) (hA : X.IsPseudoCoherentComplexFrom A n) (f : A ⟶ B)
    (hf : ∀ i, n < i → IsIso (HomologicalComplex.homologyMap f i))
    (hfn : Epi (HomologicalComplex.homologyMap f n)) :
    X.IsPseudoCoherentComplexFrom B n := by
  intro U
  obtain ⟨S, hS, h⟩ := hA U
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨P, hP, α, hα, hαn⟩ := h g hg
  let F := SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  refine ⟨P, hP, α ≫ Fc.map f, ?_, ?_⟩
  · intro i hi
    have : QuasiIsoAt f i := (quasiIsoAt_iff_isIso_homologyMap _ _).2 (hf i hi)
    have : IsIso (HomologicalComplex.homologyMap (Fc.map f) i) :=
      (quasiIsoAt_iff_isIso_homologyMap _ _).1 inferInstance
    have := hα i hi
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance
  · have : Epi (HomologicalComplex.homologyMap (Fc.map f) n) := by
      change Epi ((F.mapShortComplex ⋙ ShortComplex.homologyFunctor _).map
        ((HomologicalComplex.shortComplexFunctor _ _ n).map f))
      rw [epi_map_iff_of_natIso (ShortComplex.homologyFunctorIso F)]
      have := hfn
      exact inferInstanceAs (Epi (F.map (HomologicalComplex.homologyMap f n)))
    have := hαn
    rw [HomologicalComplex.homologyMap_comp]
    infer_instance

omit hDer in
/-- Pseudo-coherence in `D(O)` transfers along a map which is invertible on cohomology above
`n` and epic on cohomology in degree `n`: write the map as a left fraction, so that it becomes
a map of complexes with the same behaviour on cohomology. -/
private theorem isPseudoCoherentFrom_of_homologyMap
    (E F : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (hE : X.IsPseudoCoherentFrom E n) (f : E ⟶ F)
    (hf : ∀ i, n < i → IsIso ((DerivedCategory.homologyFunctor _ i).map f))
    (hfn : Epi ((DerivedCategory.homologyFunctor _ n).map f)) :
    X.IsPseudoCoherentFrom F n := by
  classical
  obtain ⟨A, hA, ⟨eA⟩⟩ := hE
  let B := DerivedCategory.Q.objPreimage F
  let eB : DerivedCategory.Q.obj B ≅ F := DerivedCategory.Q.objObjPreimageIso F
  obtain ⟨Z, g, s, hs, hfac⟩ := DerivedCategory.left_fac (eA.hom ≫ f ≫ eB.inv)
  have hg : DerivedCategory.Q.map g =
      (eA.hom ≫ f ≫ eB.inv) ≫ DerivedCategory.Q.map s := by
    rw [hfac]; simp
  refine ⟨Z, isPseudoCoherentComplexFrom_of_homologyMap X A Z n hA g ?_ ?_,
    ⟨(asIso (DerivedCategory.Q.map s)).symm ≪≫ eB⟩⟩
  · intro i hi
    have := hf i hi
    have : IsIso ((DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map g)) := by
      rw [hg]; simp only [Functor.map_comp]; infer_instance
    exact (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ i) g).1 this
  · have := hfn
    have : Epi ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Q.map g)) := by
      rw [hg]; simp only [Functor.map_comp]; infer_instance
    exact (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ n) g).1 this

omit hDer in
/-- A strictly perfect complex with a map to an object of `D(O)` which is invertible on
cohomology above `n` and epic in degree `n` makes that object `n`-pseudo-coherent. -/
private theorem isPseudoCoherentFrom_of_strictlyPerfect_approximation
    (P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (α : DerivedCategory.Q.obj P ⟶ E)
    (hα : ∀ i, n < i → IsIso ((DerivedCategory.homologyFunctor _ i).map α))
    (hαn : Epi ((DerivedCategory.homologyFunctor _ n).map α)) :
    X.IsPseudoCoherentFrom E n :=
  isPseudoCoherentFrom_of_homologyMap X _ E n
    ⟨P, isPseudoCoherentComplexFrom_of_isStrictlyPerfect_general X P hP n, ⟨Iso.refl _⟩⟩ α hα hαn

omit hDer in
/-- An object of `D(O)` whose cohomology vanishes in every degree at least `n` is
`n`-pseudo-coherent: the zero complex is strictly perfect and the zero map out of it is an
approximation. -/
private theorem isPseudoCoherentFrom_of_homology_isZero
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℤ)
    (hE : ∀ i, n ≤ i → IsZero ((DerivedCategory.homologyFunctor _ i).obj E)) :
    X.IsPseudoCoherentFrom E n := by
  classical
  let P : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ := 0
  have hPzero : IsZero P := isZero_zero _
  have hPzeroX (i : ℤ) : IsZero (P.X i) :=
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i).map_isZero hPzero
  have hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf X.O) P := by
    refine ⟨Set.finite_empty.subset ?_, fun i => ?_⟩
    · intro i hi
      simp only [Set.mem_ofPred_eq] at hi
      exact False.elim (hi (hPzeroX i))
    · exact isDirectSummandOfFiniteFree_of_isZero _ _ (hPzeroX i)
  have hz (i : ℤ) : IsZero ((DerivedCategory.homologyFunctor _ i).obj
      (DerivedCategory.Q.obj P)) :=
    (DerivedCategory.homologyFunctor _ i).map_isZero (DerivedCategory.Q.map_isZero hPzero)
  refine isPseudoCoherentFrom_of_strictlyPerfect_approximation X P hP E n 0 ?_ ?_
  · intro i hi
    exact (hz i).isIso (hE i (by omega)) _
  · have : IsIso ((DerivedCategory.homologyFunctor _ n).map
        (0 : DerivedCategory.Q.obj P ⟶ E)) := (hz n).isIso (hE n le_rfl) _
    infer_instance

omit hDer in
/-- **An object of `D(O)` whose cohomology vanishes in every degree at least `t` is
`t`-pseudo-coherent**: the zero complex is strictly perfect over every object of the site and
the zero map out of it is an approximation in degree `t`. -/
theorem isPseudoCoherentFrom_of_isLE_sub_one
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (t : ℤ)
    (hE : E.IsLE (t - 1)) :
    X.IsPseudoCoherentFrom E t :=
  isPseudoCoherentFrom_of_homology_isZero X E t fun i hi => by
    have := hE
    exact DerivedCategory.isZero_of_isLE E (t - 1) i (by omega)

omit hDer in
/-- **Stacks 08FU (2), the degree-free criterion.** An object of `D(O)` is pseudo-coherent
exactly when it is `n`-pseudo-coherent for every `n`. -/
alias isPseudoCoherent_iff_forall_isPseudoCoherentFrom := isPseudoCoherent_iff_forall

omit hDer in
/-- A strictly perfect complex with a map to an object of `D(O)` which is invertible on
cohomology above `n` and epic in degree `n` makes that object `n`-pseudo-coherent. -/
alias isPseudoCoherentFrom_of_isStrictlyPerfect_approximation :=
  isPseudoCoherentFrom_of_strictlyPerfect_approximation

omit hDer in
/-- An object of `D(O)` whose cohomology vanishes in every degree at least `n` is
`n`-pseudo-coherent. -/
alias isPseudoCoherentFrom_of_forall_isZero_homology := isPseudoCoherentFrom_of_homology_isZero

omit hDer in
/-- If both summands of a biproduct are `N`-pseudo-coherent for some `N ≥ n` and the biproduct
is `n`-pseudo-coherent, then both summands are `n`-pseudo-coherent. The descent is through the
split distinguished triangles, by Stacks 08FV (1). -/
private theorem isPseudoCoherentFrom_biprod_of_high
    (A B : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n N : ℤ) (hnN : n ≤ N)
    (hA : X.IsPseudoCoherentFrom A N) (hB : X.IsPseudoCoherentFrom B N)
    (hAB : X.IsPseudoCoherentFrom (A ⊞ B) n) :
    X.IsPseudoCoherentFrom A n ∧ X.IsPseudoCoherentFrom B n :=
  summands_of_biprod_step (fun i E => X.IsPseudoCoherentFrom E i)
    (fun _ _ _ e h => isPseudoCoherentFrom_of_iso X _ h e.symm)
    (fun hni E h => isPseudoCoherentFrom_mono_general X E h hni)
    (fun i Cc Dd hC hCD =>
      isPseudoCoherentFrom_of_distinguished_one_general X i (binaryBiproductTriangle Cc Dd)
        (binaryBiproductTriangle_distinguished Cc Dd) hC hCD)
    A B n N hnN hA hB hAB

/-- **Stacks 08FW**, at independent site, morphism and module universes. Let `(C, O)` be a
ringed site and `n : ℤ`. If `K ⊞ L` is `n`-pseudo-coherent in `D(O)`, then so is `K`.

Over an object `V` of the site carrying a strictly perfect approximation of `(K ⊞ L)|_V`, the
cohomology of `K|_V` and of `L|_V` vanishes above the support of the approximation, so both are
`N`-pseudo-coherent for that `N`; descending through the split distinguished triangles makes
`K|_V` and `L|_V` `n`-pseudo-coherent, and Stacks 08FU (3) globalizes that. -/
@[stacks 08FW "m-pseudo-coherent, first summand, general universes"]
theorem isPseudoCoherentFrom_left_of_biprod_general
    (K L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (h : X.IsPseudoCoherentFrom (K ⊞ L) n) : X.IsPseudoCoherentFrom K n := by
  classical
  let A := DerivedCategory.Q.objPreimage K
  let B := DerivedCategory.Q.objPreimage L
  let eA : DerivedCategory.Q.obj A ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let eB : DerivedCategory.Q.obj B ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let : PreservesBinaryBiproducts
      (DerivedCategory.Q (C := SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e : DerivedCategory.Q.obj (A ⊞ B) ≅ K ⊞ L :=
    DerivedCategory.Q.mapBiprod A B ≪≫ biprod.mapIso eA eB
  have hAB := isPseudoCoherentComplexFrom_of_iso_general X (K ⊞ L) n h (A ⊞ B) e
  apply isPseudoCoherentFrom_of_locally_general X K n
  intro U
  obtain ⟨S, hS, hdata⟩ := hAB U
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨P, hP, α, hα, hαn⟩ := hdata f hf
  let R := SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V
  let Fc := R.mapHomologicalComplex (ComplexShape.up ℤ)
  let Fd := R.mapDerivedCategory
  let M := DerivedCategory.Q.obj (Fc.obj A)
  let N := DerivedCategory.Q.obj (Fc.obj B)
  have hα' : ∀ i : ℤ, n < i →
      IsIso ((DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map α)) := by
    intro i hi
    change IsIso ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor _ i).map α)
    rw [NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors _ i)]
    exact hα i hi
  have hαn' : Epi ((DerivedCategory.homologyFunctor _ n).map (DerivedCategory.Q.map α)) := by
    change Epi ((DerivedCategory.Q ⋙ DerivedCategory.homologyFunctor _ n).map α)
    rw [epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ n)]
    exact hαn
  have hsum₀ : (X.over V).IsPseudoCoherentFrom
      (DerivedCategory.Q.obj (Fc.obj (A ⊞ B))) n :=
    isPseudoCoherentFrom_of_strictlyPerfect_approximation (X.over V) P hP _ n
      (DerivedCategory.Q.map α) hα' hαn'
  let : PreservesBinaryBiproducts Fc := preservesBinaryBiproducts_of_preservesBiproducts _
  let : PreservesBinaryBiproducts (DerivedCategory.Q
      (C := SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V))) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let eMN : DerivedCategory.Q.obj (Fc.obj (A ⊞ B)) ≅ M ⊞ N :=
    DerivedCategory.Q.mapIso (Fc.mapBiprod A B) ≪≫
      DerivedCategory.Q.mapBiprod (Fc.obj A) (Fc.obj B)
  have hsum := isPseudoCoherentFrom_of_iso (X.over V) _ hsum₀ eMN.symm
  obtain ⟨b, hb⟩ := hP.bounded.bddAbove
  have hzero : ∀ i : ℤ, max n b + 1 ≤ i → IsZero ((Fc.obj (A ⊞ B)).homology i) := by
    intro i hi
    have hPi : IsZero (P.X i) := by
      by_contra hn
      have hib : i ≤ b := hb (by simpa only [Set.mem_ofPred_eq] using hn)
      omega
    have hHi := ShortComplex.isZero_homology_of_isZero_X₂ (P.sc i) hPi
    have : IsIso (HomologicalComplex.homologyMap α i) := hα i (by omega)
    exact hHi.of_iso (asIso (HomologicalComplex.homologyMap α i)).symm
  have hMzero : ∀ i : ℤ, max n b + 1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj M) := by
    intro i hi
    have hAi : IsZero ((Fc.obj A).homology i) :=
      isZero_map_of_retract (Fc ⋙ HomologicalComplex.homologyFunctor _ _ i)
        biprod.inl biprod.fst (by simp) (hzero i hi)
    exact hAi.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app (Fc.obj A))
  have hNzero : ∀ i : ℤ, max n b + 1 ≤ i →
      IsZero ((DerivedCategory.homologyFunctor _ i).obj N) := by
    intro i hi
    have hBi : IsZero ((Fc.obj B).homology i) :=
      isZero_map_of_retract (Fc ⋙ HomologicalComplex.homologyFunctor _ _ i)
        biprod.inr biprod.snd (by simp) (hzero i hi)
    exact hBi.of_iso ((DerivedCategory.homologyFunctorFactors _ i).app (Fc.obj B))
  have hMN := isPseudoCoherentFrom_biprod_of_high (X.over V) M N n (max n b + 1)
    (by omega) (isPseudoCoherentFrom_of_homology_isZero (X.over V) M _ hMzero)
    (isPseudoCoherentFrom_of_homology_isZero (X.over V) N _ hNzero) hsum
  exact isPseudoCoherentFrom_of_iso (X.over V) _ hMN.1
    ((R.mapDerivedCategoryFactors.app A).symm ≪≫ Fd.mapIso eA).symm

/-- **Stacks 08FW**, at independent site, morphism and module universes. If `K ⊞ L` is
`n`-pseudo-coherent in `D(O)`, then so is `L`: exchange the two summands. -/
@[stacks 08FW "m-pseudo-coherent, second summand, general universes"]
theorem isPseudoCoherentFrom_right_of_biprod_general
    (K L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (h : X.IsPseudoCoherentFrom (K ⊞ L) n) : X.IsPseudoCoherentFrom L n :=
  isPseudoCoherentFrom_left_of_biprod_general X L K n
    (isPseudoCoherentFrom_of_iso X _ h (biprod.braiding K L).symm)

/-- **Stacks 08FW**, at independent site, morphism and module universes. If `K ⊞ L` is
pseudo-coherent in `D(O)`, then so is `K`. -/
@[stacks 08FW "pseudo-coherent, first summand, general universes"]
theorem isPseudoCoherent_left_of_biprod_general
    (K L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : X.IsPseudoCoherent (K ⊞ L)) : X.IsPseudoCoherent K :=
  (isPseudoCoherent_iff_forall X K).2 fun n =>
    isPseudoCoherentFrom_left_of_biprod_general X K L n
      ((isPseudoCoherent_iff_forall X (K ⊞ L)).1 h n)

/-- **Stacks 08FW**, at independent site, morphism and module universes. If `K ⊞ L` is
pseudo-coherent in `D(O)`, then so is `L`. -/
@[stacks 08FW "pseudo-coherent, second summand, general universes"]
theorem isPseudoCoherent_right_of_biprod_general
    (K L : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : X.IsPseudoCoherent (K ⊞ L)) : X.IsPseudoCoherent L :=
  (isPseudoCoherent_iff_forall X L).2 fun n =>
    isPseudoCoherentFrom_right_of_biprod_general X K L n
      ((isPseudoCoherent_iff_forall X (K ⊞ L)).1 h n)

omit hDer in
/-- **An object of `D(O)` isomorphic to a zero object is pseudo-coherent**, at independent site,
morphism and module universes: all of its cohomology vanishes, so the zero complex approximates
it from every degree on. -/
theorem isPseudoCoherent_of_isZero_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : IsZero E) :
    X.IsPseudoCoherent E :=
  (isPseudoCoherent_iff_forall X E).2 fun n =>
    isPseudoCoherentFrom_of_homology_isZero X E n
      fun i _ => (DerivedCategory.homologyFunctor _ i).map_isZero hE

omit hDer in
/-- **Stacks 08FV without a fixed degree**, at independent site, morphism and module universes:
two out of three for pseudo-coherence in a distinguished triangle of `D(O)`.

Pseudo-coherence is `m`-pseudo-coherence for every `m`
(`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall`), and the three parts of Stacks
08FV apply degree by degree: part (1) for the third vertex, part (2) for the second and part
(3) — read at `m - 1` — for the first. -/
theorem isPseudoCoherent_of_distinguished_general
    (tri : Triangle
      (DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (htri : tri ∈ distinguishedTriangles) :
    (X.IsPseudoCoherent tri.obj₁ → X.IsPseudoCoherent tri.obj₂ →
        X.IsPseudoCoherent tri.obj₃) ∧
      (X.IsPseudoCoherent tri.obj₁ → X.IsPseudoCoherent tri.obj₃ →
        X.IsPseudoCoherent tri.obj₂) ∧
      (X.IsPseudoCoherent tri.obj₂ → X.IsPseudoCoherent tri.obj₃ →
        X.IsPseudoCoherent tri.obj₁) := by
  refine ⟨fun h₁ h₂ => (isPseudoCoherent_iff_forall X _).2 fun m => ?_,
    fun h₁ h₃ => (isPseudoCoherent_iff_forall X _).2 fun m => ?_,
    fun h₂ h₃ => (isPseudoCoherent_iff_forall X _).2 fun m => ?_⟩
  · exact isPseudoCoherentFrom_of_distinguished_one_general X m tri htri
      ((isPseudoCoherent_iff_forall X _).1 h₁ (m + 1))
      ((isPseudoCoherent_iff_forall X _).1 h₂ m)
  · exact isPseudoCoherentFrom_of_distinguished_two_general X m tri htri
      ((isPseudoCoherent_iff_forall X _).1 h₁ m) ((isPseudoCoherent_iff_forall X _).1 h₃ m)
  · obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    exact isPseudoCoherentFrom_of_distinguished_three_general X n tri htri
      ((isPseudoCoherent_iff_forall X _).1 h₂ (n + 1))
      ((isPseudoCoherent_iff_forall X _).1 h₃ n)

section DiagonalUniverses

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- **Stacks 08FW.** Let `(C, O)` be a ringed site and `n : ℤ`. If `K ⊞ L` is
`n`-pseudo-coherent in `D(O)`, then so is `K`.

Over an object `V` of the site carrying a strictly perfect approximation of `(K ⊞ L)|_V`, the
cohomology of `K|_V` and of `L|_V` vanishes above the support of the approximation, so both are
`N`-pseudo-coherent for that `N`; descending through the split distinguished triangles makes
`K|_V` and `L|_V` `n`-pseudo-coherent, and Stacks 08FU (3) globalizes that. -/
@[stacks 08FW "m-pseudo-coherent, first summand", sga "6 I 2.12" "n-pc: sum ⇒ F'"]
theorem isPseudoCoherentFrom_left_of_biprod
    (K L : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (h : X.IsPseudoCoherentFrom (K ⊞ L) n) : X.IsPseudoCoherentFrom K n :=
  isPseudoCoherentFrom_left_of_biprod_general X K L n h

/-- **Stacks 08FW.** If `K ⊞ L` is `n`-pseudo-coherent in `D(O)`, then so is `L`: exchange the
two summands and apply the previous statement. -/
@[stacks 08FW "m-pseudo-coherent, second summand", sga "6 I 2.12" "n-pc: sum ⇒ F''"]
theorem isPseudoCoherentFrom_right_of_biprod
    (K L : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (h : X.IsPseudoCoherentFrom (K ⊞ L) n) : X.IsPseudoCoherentFrom L n :=
  isPseudoCoherentFrom_left_of_biprod X L K n
    (isPseudoCoherentFrom_of_iso X _ h (biprod.braiding K L).symm)

/-- **Stacks 08FW.** If `K ⊞ L` is pseudo-coherent in `D(O)`, then so is `K`. -/
@[stacks 08FW "pseudo-coherent, first summand", sga "6 I 2.12" "pc: sum ⇒ F'"]
theorem isPseudoCoherent_left_of_biprod
    (K L : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : X.IsPseudoCoherent (K ⊞ L)) : X.IsPseudoCoherent K :=
  (isPseudoCoherent_iff_forall X K).2 fun n =>
    isPseudoCoherentFrom_left_of_biprod X K L n
      ((isPseudoCoherent_iff_forall X (K ⊞ L)).1 h n)

/-- **Stacks 08FW.** If `K ⊞ L` is pseudo-coherent in `D(O)`, then so is `L`. -/
@[stacks 08FW "pseudo-coherent, second summand"]
theorem isPseudoCoherent_right_of_biprod
    (K L : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : X.IsPseudoCoherent (K ⊞ L)) : X.IsPseudoCoherent L :=
  (isPseudoCoherent_iff_forall X L).2 fun n =>
    isPseudoCoherentFrom_right_of_biprod X K L n
      ((isPseudoCoherent_iff_forall X (K ⊞ L)).1 h n)

end DiagonalUniverses

/-- **Stacks 08FU, part (3), the all-degrees companion of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`.**  If for every integer
`m` the object `E` of `D(O)` is `m`-pseudo-coherent locally on `X` — on the slices over the
members of some covering sieve of each object, the sieve being allowed to depend on `m` — then
`E` is pseudo-coherent.

The hypothesis is the degreewise local one and the conclusion is the all-degrees condition of
Stacks 08FT (3), which asks for **one** complex that is `m`-pseudo-coherent for every `m`; the
quantifier swap is
`AlgebraicGeometry.RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom`, whose content
is the forward direction of Stacks 08FU (2).  It is not obtained by applying the degreewise
statement in each degree separately, which would only give a family of complexes. -/
theorem isPseudoCoherent_of_locally_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ m : ℤ, ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        (X.over V).IsPseudoCoherentFrom
          ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategory.obj E) m) :
    X.IsPseudoCoherent E :=
  (isPseudoCoherent_iff_forall_isPseudoCoherentFrom X E).2 fun m =>
    isPseudoCoherentFrom_of_locally_general X E m (h m)

end Main

end AlgebraicGeometry.RingedSite

end

