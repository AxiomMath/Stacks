module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatnessAndRightExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionWithFlatTermsSurjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.Defs
public import StacksFrontier.Homology.KFlat.BifunctorSingleSecondFactor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.FlatCokernel
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tor amplitude bounded below is a bounded below K-flat representative with flat terms

Let `(C, O)` be a ringed site, let `T` be a derived tensor product on `D(O)` in the sense of
`Stacks.SheafOfModules.DerivedTensorProduct`, and let `a` be an integer. An object `E` of `D(O)`
has *Tor amplitude in `[a, ∞]`* when `E ⊗^L_O F[0]` has no cohomology below `a`, for every sheaf
of `O`-modules `F`. This file proves that this happens exactly when `E` is represented by a
K-flat complex of flat `O`-modules vanishing in every degree below `a`.

## Main definitions

* `Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE`: Tor amplitude in the
  half-infinite interval `[a, ∞]`.

## Main results

* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_iff_exists_kFlatRepresentative`:
  **Stacks 0F1M, the equivalence.** Tor amplitude in `[a, ∞]` is equivalent to being represented
  by a K-flat complex of flat `O`-modules vanishing below `a`.
* `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_exactAt_rowComplex`: the
  cokernel of `d^{a-1}` of a complex whose terms in the two degrees `a - 1` and `a` are flat and
  whose termwise tensor products are exact at `a - 1` is flat. This is the hypothesis Stacks 08G0
  really uses.
* `Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_kFlatRepresentative`: the easy
  direction, which needs neither flatness of the terms nor the diagonal universe hypotheses.

## Implementation notes

The source's argument, and the shape of the proof. A K-flat resolution `K` of `E` with flat
terms exists by Stacks 06YS; the Tor-amplitude hypothesis makes the termwise complex
`p ↦ K^p ⊗_O F` exact below `a` for every `F`, so `N = Coker(d^{a-1})` is a flat `O`-module;
and the representative is `τ_{≥ a}K`, whose terms are those of `K` above `a`, `N` in degree `a`
and zero below. It is K-flat by Stacks 0G7B applied to
`0 ⟶ Ker(π) ⟶ K ⟶ τ_{≥ a}K ⟶ 0`, whose left term is bounded above with flat terms — flat by
Stacks 03EY, bounded above because `π` is degreewise an isomorphism above `a`
(`HomologicalComplex.isIso_πTruncGE_f` at the embedding `ComplexShape.embeddingUpIntGE`, whose
non-boundary degrees are exactly those strictly above `a`) — and hence K-flat
by Stacks 06YQ. Finally `π` is a quasi-isomorphism because `E` itself is `≥ a`, which is the
Tor-amplitude hypothesis read at `F = O` through the unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`.

Why the flat-cokernel step is not Stacks 08G0 as formalized.
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude` takes the complex
to be *bounded above*, as the source's 08G0 does, and uses that only to get K-flatness out of
Stacks 06YQ. The resolution produced by Stacks 06YS is not bounded above, and no upper
Tor-amplitude bound is available here, so that statement does not apply. The two hypotheses are
weakened here to the ones the argument uses — K-flatness of the complex, and vanishing of the
derived tensor cohomology below `a` only — and the real content, the diagram chase
`Stacks.Cohomology.TorAmplitude.FlatCokernel.preservesMonomorphisms_tensor_cokernel` and the
identification `CochainComplex.KFlatBifunctor.totalSingleIso` of `Tot(K ⊗_O F[0])` with the
termwise complex, is reused rather than reproved.

The pullback-stability clause. The source adds that the representative may be chosen so that its
pullback along every morphism of ringed sites is again K-flat with flat terms. In the presence of
Stacks 0G7E — the pullback of a K-flat complex with flat terms is K-flat with flat terms — that
clause has no content beyond the equivalence proved here: *every* representative as in (2) has
the property, so no choice is involved. It is stated, with both of its halves, in the namespace
`Stacks.SheafOfModules` by
`DerivedTensorProduct.exists_pullbackStable_kFlatRepresentative_of_hasTorAmplitudeGE`, which
applies `AlgebraicGeometry.RingedToposSiteHom.kFlat_pullbackComplex` and
`AlgebraicGeometry.RingedToposSiteHom.isFlat_pullbackComplex_X` to the complex this file
produces. It is kept in its own module because that pair lives downstream of this one.

Universes. The easy direction and the flat-cokernel step keep all four universes free, as the Tor
amplitude predicate itself does. The equivalence collapses the site's two universes and the
section universe, because Stacks 06YS, 0G7B and the unit law are available only there.

## References

* [Stacks Project, Tag 0F1M](https://stacks.math.columbia.edu/tag/0F1M)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G0](https://stacks.math.columbia.edu/tag/08G0)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 0G7B](https://stacks.math.columbia.edu/tag/0G7B)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
* [Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w d

/-- The kernel sequence of the projection `K ⟶ τ_{≥ a}K` is short exact. -/
private theorem CochainComplex.shortExact_kernelSequence_πTruncGE {C : Type*} [Category C]
    [Abelian C] (K : CochainComplex C ℤ) (a : ℤ) :
    (ShortComplex.kernelSequence (K.πTruncGE a)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance
    (inferInstanceAs (Epi (HomologicalComplex.πTruncGE K (ComplexShape.embeddingUpIntGE a))))

/-- The kernel of the projection `K ⟶ τ_{≥ a}K` is strictly concentrated in degrees `≤ a`. -/
private theorem CochainComplex.isStrictlyLE_kernelSequence_πTruncGE {C : Type*} [Category C]
    [Abelian C] (K : CochainComplex C ℤ) (a : ℤ) :
    (ShortComplex.kernelSequence (K.πTruncGE a)).X₁.IsStrictlyLE a := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have _ : IsIso ((K.πTruncGE a).f i) :=
    K.isIso_πTruncGE_f _
      (show (ComplexShape.embeddingUpIntGE a).f (i - a).natAbs = i by
        rw [ComplexShape.embeddingUpIntGE_f, Int.natAbs_of_nonneg (by omega)]
        omega)
      (by rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]; omega)
  have hSi := (CochainComplex.shortExact_kernelSequence_πTruncGE K a).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i)
  have _ := hSi.mono_f
  exact IsZero.of_mono_eq_zero _
    (hSi.exact.mono_g_iff.1 (inferInstanceAs (Mono ((K.πTruncGE a).f i))))

namespace Stacks.SheafOfModules.DerivedTensorProduct

-- The sections universe `w` is free, so Mathlib's size-restricted instances do not supply the
-- sheaf-condition composition that `AlgebraicGeometry.SheafOfModules.IsFlat` is stated through.
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section FreeUniverses

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)]

/-- **Stacks 08FZ (1) for the half-infinite interval `[a, ∞]`.** An object `E` of `D(O)` has
*Tor amplitude in `[a, ∞]`* for the derived tensor product `T` if, for every sheaf of
`O`-modules `F`, the derived tensor product of `E` with `F` placed in degree zero has vanishing
cohomology in every degree below `a`. -/
def HasTorAmplitudeGE (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (a : ℤ) : Prop :=
  ∀ (F : RingedSite.Modules.{u, v, w} X) (i : ℤ), i < a →
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
      ((T.tensor.obj E).obj
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)))

/-- Tor amplitude in a bounded interval bounds the amplitude below. -/
theorem hasTorAmplitudeGE_of_hasTorAmplitude (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (a b : ℤ)
    (hE : HasTorAmplitude T E a b) :
    HasTorAmplitudeGE T E a :=
  fun F i hi => hE F i (by simp only [Set.mem_Icc, not_and_or, not_le]; exact Or.inl hi)

/-- Tor amplitude in `[a, ∞]` transports along an isomorphism of `D(O)`. -/
theorem HasTorAmplitudeGE.of_iso {T : DerivedTensorProduct.{u, v, w, d} X}
    {E E' : RingedSite.DerivedModules.{u, v, w, d} X} {a : ℤ}
    (hE : HasTorAmplitudeGE T E a) (e : E' ≅ E) :
    HasTorAmplitudeGE T E' a := fun F i hi =>
  (hE F i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
      ((T.tensor.mapIso e).app
        ((DerivedCategory.singleFunctor (RingedSite.Modules.{u, v, w} X) 0).obj F)))

/-- For a K-flat complex `K`, the cohomology of `K ⊗^L_O F₀` is that of the total tensor
complex `Tot(K ⊗_O F₀)`. -/
private def homologyTensorIso (T : DerivedTensorProduct.{u, v, w, d} X)
    (K F₀ : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (hKflat : IsKFlat X.O K) (i : ℤ) :
    (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).obj
      ((T.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj F₀)) ≅
    (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj F₀).homology i :=
  (DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
      (T.comparisonLeft K F₀ hKflat) ≪≫
    (DerivedCategory.homologyFunctorFactors (RingedSite.Modules.{u, v, w} X) i).app _

/-- **Stacks 0F1M, the implication (2) `⇒` (1).** A K-flat complex which vanishes in every degree
below `a` represents an object of Tor amplitude in `[a, ∞]`.

Flatness of the terms is not needed: K-flatness of the left factor already makes the derived
tensor product with `F[0]` the ordinary total tensor complex `Tot(K ⊗_O F[0])`, which is the
termwise complex `p ↦ K^p ⊗_O F` and so vanishes wherever `K` does. -/
theorem hasTorAmplitudeGE_of_kFlatRepresentative (T : DerivedTensorProduct.{u, v, w, d} X)
    (E : RingedSite.DerivedModules.{u, v, w, d} X) (a : ℤ)
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ)
    (hKflat : IsKFlat X.O K)
    (hzero : ∀ i : ℤ, i < a → IsZero (K.X i))
    (e : DerivedCategory.Q.obj K ≅ E) :
    HasTorAmplitudeGE T E a := by
  intro F i hi
  exact ((CochainComplex.KFlatBifunctor.isZero_homology_mapBifunctor_single
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) K F i (hzero i hi)).of_iso
    (homologyTensorIso T K _ hKflat i)).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, v, w} X) i).mapIso
      ((T.tensor.mapIso e).app _).symm)

/-- **A K-flat complex of Tor amplitude in `[a, ∞]` has exact termwise tensor products below
`a`.** The degree-`i` cohomology of `K ⊗^L_O F[0]` is the degree-`i` cohomology of
`Tot(K ⊗_O F[0])`, because `K` is K-flat, and that total complex is the termwise complex
`p ↦ K^p ⊗_O F`. -/
theorem exactAt_rowComplex_of_hasTorAmplitudeGE (T : DerivedTensorProduct.{u, v, w, d} X)
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (a i : ℤ)
    (hKflat : IsKFlat X.O K)
    (hamp : HasTorAmplitudeGE T (DerivedCategory.Q.obj K) a)
    (F : RingedSite.Modules.{u, v, w} X) (hi : i < a) :
    (CochainComplex.KFlatBifunctor.rowComplex
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) K F).ExactAt i := by
  let F₀ := (HomologicalComplex.single (RingedSite.Modules.{u, v, w} X)
    (ComplexShape.up ℤ) 0).obj F
  let L := ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj K).obj F₀
  refine HomologicalComplex.ExactAt.of_iso (K := L) ?_
    (CochainComplex.KFlatBifunctor.totalSingleIso
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) K F)
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (hamp F i hi).of_iso (homologyTensorIso T K F₀ hKflat i).symm

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) (ComplexShape.up ℤ)] in
/-- **The flat-cokernel step of Stacks 08G0, on the hypothesis the argument actually uses.** Let
`K` be a complex whose terms in the two degrees `a - 1` and `a` are flat `O`-modules and whose
termwise tensor product with every `O`-module is exact at `a - 1`. Then the cokernel of the
differential `K^{a-1} ⟶ K^a` is a flat `O`-module.

Exactness at `a - 1` says that `K^{a-2} ⊗ F ⟶ K^{a-1} ⊗ F ⟶ K^a ⊗ F` is exact for every `F`, and
that is exactly what makes `- ⊗_O Coker(d^{a-1})` preserve monomorphisms; preserving
monomorphisms plus right exactness gives exactness, by
`CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels`. Flatness is exactness
of tensoring on the *right*, while the functors above tensor on the left; the two are exchanged
by the braiding `Stacks.SheafOfModules.Tensor.sheafTensorBraiding`.

Only the two degrees `a - 1` and `a` are asked to be flat; nothing is assumed about the terms of
`K` in any other degree, and in particular not about `K^{a-2}`, which the exactness hypothesis
mentions. -/
theorem isFlat_cokernel_of_exactAt_rowComplex
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (a : ℤ)
    (hflatPrev :
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K.X (a - 1)))
    (hflatTop : AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K.X a))
    (hexact : ∀ F : RingedSite.Modules.{u, v, w} X,
      (CochainComplex.KFlatBifunctor.rowComplex
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O) K F).ExactAt (a - 1)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O)
      (cokernel (K.d (a - 1) a)) := by
  let T' := Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O
  let S := K.sc' (a - 2) (a - 1) a
  let _ : ∀ M, PreservesFiniteColimits (T'.obj M) := fun M =>
    let := Stacks.SheafOfModules.preservesColimits_sheafTensorObj X.O M
    PreservesColimitsOfSize.preservesFiniteColimits _
  let _ : ∀ M, PreservesFiniteColimits (T'.flip.obj M) := fun M =>
    let := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj X.O M
    PreservesColimitsOfSize.preservesFiniteColimits _
  let _ : PreservesFiniteLimits (T'.obj S.X₂) :=
    (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat X.O hflatPrev).1
  let _ : PreservesFiniteLimits (T'.obj S.X₃) :=
    (Stacks.SheafOfModules.exact_sheafTensorObj_of_isFlat X.O hflatTop).1
  have hS (M : RingedSite.Modules.{u, v, w} X) : (S.map (T'.flip.obj M)).Exact :=
    (HomologicalComplex.exactAt_iff' _ (a - 2) (a - 1) a
      ((ComplexShape.up ℤ).prev_eq' (show a - 2 + 1 = a - 1 by omega))
      ((ComplexShape.up ℤ).next_eq' (show a - 1 + 1 = a by omega))).1 (hexact M)
  let _ := Stacks.Cohomology.TorAmplitude.FlatCokernel.preservesMonomorphisms_tensor_cokernel
    T' S hS
  have hcoker : PreservesFiniteColimits (T'.obj (cokernel S.g)) :=
    Stacks.SheafOfModules.preservesFiniteColimits_sheafTensorObj X.O (cokernel S.g)
  let _ : ∀ {M N : RingedSite.Modules.{u, v, w} X} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (T'.obj (cokernel S.g)) := fun _ =>
    (hcoker.preservesFiniteColimits WalkingParallelPair).preservesColimit
  let _ := Functor.preservesHomology_of_preservesMonos_and_cokernels (T'.obj (cokernel S.g))
  let _ : ∀ {M N : RingedSite.Modules.{u, v, w} X} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (T'.obj (cokernel S.g)) :=
    fun f => Functor.PreservesHomology.preservesKernel _ f
  exact Stacks.SheafOfModules.isFlat_of_exactFunctor_sheafTensorFlip X.O _
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).app (cokernel S.g))
      ((exactFunctor_iff _).2
        ⟨Functor.preservesFiniteLimits_of_preservesKernels _, inferInstance⟩))

/-- **Stacks 08G0 for a K-flat complex and a lower Tor bound.** The cokernel of the differential
into the lowest degree of the Tor-amplitude interval of a K-flat complex of flat `O`-modules is a
flat `O`-module.

`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_cokernel_of_hasTorAmplitude` is the same
conclusion for a *bounded above* complex and a bounded interval; there boundedness is used only
to produce K-flatness out of Stacks 06YQ, which is assumed here instead, because the K-flat
resolution of Stacks 06YS is not bounded above. -/
theorem isFlat_cokernel_of_hasTorAmplitudeGE (T : DerivedTensorProduct.{u, v, w, d} X)
    (K : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ) (a : ℤ)
    (hKflat : IsKFlat X.O K)
    (hflat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) (K.X i))
    (hamp : HasTorAmplitudeGE T (DerivedCategory.Q.obj K) a) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O)
      (cokernel (K.d (a - 1) a)) :=
  isFlat_cokernel_of_exactAt_rowComplex K a (hflat (a - 1)) (hflat a) fun F =>
    exactAt_rowComplex_of_hasTorAmplitudeGE T K a (a - 1) hKflat hamp F (by omega)

end FreeUniverses

/-- The terms of `τ_{≥ a}P` are flat when those of `P` and the cokernel of `d_P^{a-1}` are. -/
private theorem isFlat_truncGE_X_of_isFlat_cokernel {X : RingedSite.{u, u, u}}
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (P : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ) (a : ℤ)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (P.X i))
    (hcoker : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      (cokernel (P.d (a - 1) a))) (i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) ((P.truncGE a).X i) := by
  rcases lt_trichotomy i a with hlt | heq | hgt
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_isZero X.O
      ((P.truncGE a).isZero_of_isStrictlyGE a i hlt)
  · rw [heq]
    exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O
      ((IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (a - 1) a (by simp))
        (colimit.isColimit _)).symm ≪≫ (P.truncGEXIsoOpcycles a).symm) hcoker
  · exact AlgebraicGeometry.SheafOfModules.IsFlat.of_iso X.O
      (P.truncGEXIso a i hgt).symm (hflat i)

section SmallSite

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

/-- **An object of Tor amplitude in `[a, ∞]` is concentrated in degrees `≥ a`.** Its derived
tensor product with the structure sheaf in degree zero is itself, by the unit law
`Stacks.SheafOfModules.DerivedTensorProduct.unitIso`. -/
theorem isZero_homology_of_hasTorAmplitudeGE (T : DerivedTensorProduct.{u, u, u, d} X)
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) (hE : HasTorAmplitudeGE T E a)
    (i : ℤ) (hi : i < a) :
    IsZero ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} X) i).obj E) :=
  (hE (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) i hi).of_iso
    ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u, u, u} X) i).mapIso
      (T.unitIso E).symm)

/-- **Stacks 0F1M, the implication (1) `⇒` (2).** An object of `D(O)` with Tor amplitude in
`[a, ∞]` is represented by a K-flat complex of flat `O`-modules vanishing in every degree below
`a`.

The complex is `τ_{≥ a}K` for `K` a K-flat resolution with flat terms (Stacks 06YS): the only
term that changes is the one in degree `a`, which becomes `Coker(d_K^{a-1})`, flat by the
Tor-amplitude hypothesis. -/
theorem exists_kFlatRepresentative_of_hasTorAmplitudeGE
    (T : DerivedTensorProduct.{u, u, u, d} X)
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) (hE : HasTorAmplitudeGE T E a) :
    ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
      IsKFlat X.O K ∧
      (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
      (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨P, p, hPkflat, hPflat, hp, -⟩ :=
    Stacks.SheafOfModules.exists_isKFlat_isFlat_quasiIso_epi X
      (DerivedCategory.Q.objPreimage E)
  have _ : QuasiIso p := hp
  have eP : DerivedCategory.Q.obj P ≅ E :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso E
  have hPamp : HasTorAmplitudeGE T (DerivedCategory.Q.obj P) a := hE.of_iso eP
  have _ : P.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff, DerivedCategory.isGE_iff]
    exact isZero_homology_of_hasTorAmplitudeGE T _ a hPamp
  have hTruncFlat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) ((P.truncGE a).X i) :=
    isFlat_truncGE_X_of_isFlat_cokernel P a hPflat
      (isFlat_cokernel_of_hasTorAmplitudeGE T P a hPkflat hPflat hPamp)
  have hS : (ShortComplex.kernelSequence (P.πTruncGE a)).ShortExact :=
    CochainComplex.shortExact_kernelSequence_πTruncGE P a
  have hKerFlat : ∀ i : ℤ,
      AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
        ((ShortComplex.kernelSequence (P.πTruncGE a)).X₁.X i) := fun i =>
    Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact X.O
      ((ShortComplex.kernelSequence (P.πTruncGE a)).map
        (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
      (hS.map_of_exact (HomologicalComplex.eval _ (ComplexShape.up ℤ) i))
      (hPflat i) (hTruncFlat i)
  have hKerKFlat : IsKFlat X.O (ShortComplex.kernelSequence (P.πTruncGE a)).X₁ :=
    Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O _
      ⟨a, CochainComplex.isStrictlyLE_kernelSequence_πTruncGE P a⟩ hKerFlat
  have hTruncKFlat : IsKFlat X.O (P.truncGE a) :=
    Stacks.SheafOfModules.KFlatTwoOutOfThree.kFlat_right_of_shortExact X.O
      (ShortComplex.kernelSequence (P.πTruncGE a)) hS hTruncFlat hKerKFlat hPkflat
  exact ⟨P.truncGE a, hTruncKFlat, hTruncFlat,
    fun i hi => (P.truncGE a).isZero_of_isStrictlyGE a i hi,
    ⟨(asIso (DerivedCategory.Q.map (P.πTruncGE a))).symm ≪≫ eP⟩⟩

/-- **Stacks 0F1M, for any derived tensor product.** An object `E` of `D(O)` on a ringed site has
Tor amplitude in `[a, ∞]` for `T` exactly when it is represented by a K-flat complex of flat
`O`-modules vanishing in every degree below `a`. The tag is registered on its instance at the
constructed derived tensor product,
`Stacks.SheafOfModules.hasTorAmplitudeGE_iff_exists_kFlatRepresentative`. -/
theorem hasTorAmplitudeGE_iff_exists_kFlatRepresentative
    (T : DerivedTensorProduct.{u, u, u, d} X)
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (a : ℤ) :
    HasTorAmplitudeGE T E a ↔
      ∃ K : CochainComplex (RingedSite.Modules.{u, u, u} X) ℤ,
        IsKFlat X.O K ∧
        (∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧
        Nonempty (DerivedCategory.Q.obj K ≅ E) where
  mp hE := exists_kFlatRepresentative_of_hasTorAmplitudeGE T E a hE
  mpr := by
    rintro ⟨K, hKflat, -, hzero, ⟨e⟩⟩
    exact hasTorAmplitudeGE_of_kFlatRepresentative T E a K hKflat hzero e

end SmallSite

end Stacks.SheafOfModules.DerivedTensorProduct

end
