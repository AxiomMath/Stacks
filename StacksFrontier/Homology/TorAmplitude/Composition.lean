module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Homology.KFlat.Resolution
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.TorAmplitude.FaithfullyFlat
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Triangle

/-!
# Tor amplitudes add under derived tensor product

Let `A → B` be a map of commutative rings and let `K`, `L` be complexes of `B`-modules. If `K` has
Tor amplitude in `[a, b]` over `B` and `L`, read as a complex of `A`-modules, has Tor amplitude in
`[c, d]` over `A`, then `K ⊗_B^L L`, read as a complex of `A`-modules, has Tor amplitude in
`[a + c, b + d]` over `A`. This is Stacks 0B66. Taking `L = B[0]` and using the right unit of the
derived tensor product gives Stacks 066K: if `B` has Tor dimension at most `d` over `A`, then
a complex of `B`-modules with Tor amplitude `[a, b]` over `B` has Tor amplitude `[a - d, b]` over
`A`.

## Main results

* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_derivedTensor`: the Stacks 0B66 statement,
  universally quantified over the certified derived tensor bifunctor.
* `StacksDraft.TorAmplitude.hasTorAmplitudeIn_restrictScalars_of_torDimensionLE`: likewise for
  Stacks 066K.

Neither carries a `@[stacks]` attribute. Both quantify over the certificate, where their sources
state the result at the canonical derived tensoring, so neither exhibits its source's claim on its
own. The tagged endpoints are in `StacksFrontier.Homology.TorAmplitude.CompositionCanonical`, stated
at the canonical certificate of `StacksFrontier.Homology.TorAmplitude.CanonicalCertificate` — and
for 066K over the source's three independent universes. The theorems here are what those endpoints
are proved from.

## Implementation notes

### Which certificate the statement is over

Stacks 0652 states Tor amplitude relative to a bifunctor `derivedTensor` certified by a comparison
with *termwise* tensoring by a module together with the universal property making
`- ⊗ᴸ M[0]` the total left derived functor of `- ⊗ M`. That certificate constrains the bifunctor
only through `derivedTensor.flip.obj (M[0])` for **modules** `M`, so it says nothing at all about
the value of the bifunctor at a general complex in its second variable. Stacks 0B66 evaluates the
bifunctor at `Q L` for an arbitrary complex `L`, and therefore cannot be proved — indeed cannot be
stated with any content — over the 0652 certificate alone.

The statements below are therefore taken over
`CochainComplex.DerivedTensor.DerivedTensorProduct`, the certified bifunctor of Stacks 064M and
0BYI, which carries a comparison with the ordinary total tensor product at every *pair* of K-flat
complexes and is exact in both variables. This is the same choice, for the same reason, as
`StacksDraft.TorAmplitude.hasTorAmplitudeAbove_iff_exists_kFlat_flat_representative` (Stacks 0BYL).
Tor amplitude itself is spelled by `Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn` against the
derived tensoring datum that such a bifunctor determines (`derivedTensoringOfCertified`); on the
nose this is the same proposition as `StacksDraft.TorAmplitude.HasTorAmplitude` of Stacks 0652 for
the same bifunctor, and `hasTorAmplitudeIn_iff_hasTorAmplitude` records the translation, which is
how Stacks 0654 is applied below.

`DerivedTensorProduct` puts the module carriers in the universe of the ring, so a statement
relating two rings in *different* universes cannot be phrased against it. For those,
`derivedTensoringOfCertifiedGeneral` builds the datum from
`CochainComplex.DerivedTensor.DerivedTensorProductGeneral`, whose module universe is free, and
Tor amplitude is `Stacks.TorAmplitudeTriangle.HasTorAmplitudeInLarge`. Stacks 0H75 in
`StacksFrontier.Homology.TorAmplitude.Nilpotent` is stated that way; the statements in this file are
not, because their two rings are related by an `Algebra` instance and so share a universe
already.

On the `B` side the 0652 certificate is *also* assumed, and used: Stacks 0654 turns the
Tor-amplitude hypothesis on `K` into a representative by a complex of flat modules concentrated in
degrees `[a, b]`, and 0654 is stated over the 0652 certificate. Nothing else uses it.

### The shape of the proof

Replace `K` by a complex `E` of flat `B`-modules with `E^i = 0` outside `[a, b]` (Stacks 0654), and
`L` by a K-flat resolution `F` (Stacks 06Y4). Then `E` is K-flat (Stacks 064K), so the K-flat
comparison of the bifunctor identifies `K ⊗_B^L L` with `Q (E ⊗ F)`.

To bound the Tor amplitude over `A` of `E ⊗ F` after restriction of scalars, resolve the `A`-module
`M` by a bounded above complex `P` of projectives and use the projection formula
`restrict (X ⊗_B (B ⊗_A P)) ≅ (restrict X) ⊗_A P` of Stacks 0DJF
(`StacksDraft.TorAmplitude.FaithfullyFlat.restrictTensorLeftExtendIso`) in both directions: it
converts the hypothesis on `F` into cohomological bounds `[c, d]` for `W = F ⊗_B (B ⊗_A P)`, and it
converts a bound for `(E ⊗ F) ⊗_B (B ⊗_A P) ≅ E ⊗ W` back into the required statement over `A`. The
bound for `E ⊗ W` is the substantive point: it is the spectral sequence of the double complex
`E ⊗ W`, formalized here as an induction on the number of nonzero columns of a bicomplex, splitting
off the bottom column by the short exact sequence
`StacksDraft.TorAmplitude.FaithfullyFlat`-free machinery of
`StacksFrontier.Algebra.Homology.TotalComplexQuasiIso` provides
(`totalBottomSES_shortExact`), whose two outer terms are the total complex of the truncated
bicomplex and the total complex of a single column.

The bridge between Tor amplitude against the certified bifunctor and the resolution-computed
cohomology used by the projection formula is `isZero_derivedTensor_iff_tensorResolution`. It holds
for an arbitrary complex, obtained from the K-flat case by a K-flat resolution (Stacks 06Y4); the
K-flat case is `isZero_derivedTensor_iff_tensorResolution_of_kFlat`, which is the bifunctor's own
K-flat comparison.

## References

* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
* [Stacks Project, Tag 066K](https://stacks.math.columbia.edu/tag/066K)
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

namespace StacksDraft.TorAmplitude

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false

@[expose] public section

/-! ### Tor amplitude against a certified derived tensor bifunctor -/

section Certificate

variable {R : Type u} [CommRing R]

/-- The derived tensoring datum of Stacks 0655 determined by a certified derived tensor
bifunctor: tensoring on the right by the module placed in degree zero, which commutes with the
shift and is triangulated because the bifunctor is exact in its first variable. -/
public noncomputable def derivedTensoringOfCertified
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R) :
      Stacks.TorAmplitudeTriangle.DerivedTensoring R where
  derTensor M := T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)
  commShift _ := T.commShift_left _
  isTriangulated _ := T.exact_left _

/-- The derived tensoring datum determined by a certified derived tensor bifunctor whose module
carriers live in a universe `max u v` independent of the universe of `R`: tensoring on the right
by the module placed in degree zero, which commutes with the shift and is triangulated because the
bifunctor is exact in its first variable.

This is `derivedTensoringOfCertified` with the module universe freed, and it is what a statement
relating two rings in *different* universes has to be phrased against; at `v = u` the two agree,
since `CochainComplex.DerivedTensor.DerivedTensorProduct.toGeneral` is the identity on every field.
The same-universe version is kept because existing endpoints are stated against it. -/
public noncomputable def derivedTensoringOfCertifiedGeneral
    (T : CochainComplex.DerivedTensor.DerivedTensorProductGeneral.{u, v} R) :
    Stacks.TorAmplitudeTriangle.DerivedTensoringLarge.{u, v} R where
  derTensor M :=
    T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
  commShift _ := T.commShift_left _
  isTriangulated _ := T.exact_left _

/-- Tor amplitude against the derived tensoring datum of a certified derived tensor bifunctor is
the Tor amplitude of Stacks 0652 for that bifunctor. The two differ only in how the excluded
degrees are written. -/
public theorem hasTorAmplitudeIn_iff_hasTorAmplitude
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ T.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T) K a b ↔
      HasTorAmplitude T.tensor comparison isLeftDerived K a b := by
  refine ⟨fun h M i hi => ?_, fun h M i hi => ?_⟩ <;>
    exact h M i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi)

/-- At a K-flat complex `E`, the cohomology of the certified derived tensor product with a module
`M` placed in degree zero is the cohomology of `E ⊗ P` for any bounded above resolution `P` of `M`
by projective modules: `P` is K-flat, so the bifunctor's K-flat comparison applies to the pair
`(E, P)`. -/
private theorem isZero_derivedTensor_iff_tensorResolution_of_kFlat
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (E : CochainComplex (ModuleCat.{u} R) ℤ) (hE : E.KFlat) (M : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (π : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
    (hPLE : P.IsStrictlyLE m) (hPproj : ∀ n : ℤ, Projective (P.X n)) (hπ : QuasiIso π) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj (DerivedCategory.Q.obj E)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) ↔
      IsZero (((tensorLeft E).obj P).homology i) := by
  have := hPLE
  have := hπ
  have hPKF : P.KFlat := kFlat_of_isStrictlyLE_projective P m hPproj
  let eM : (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M
  let eP : DerivedCategory.Q.obj P ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M :=
    asIso (DerivedCategory.Q.map π) ≪≫ eM.symm
  let iso : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj (DerivedCategory.Q.obj E)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) ≅
      ((tensorLeft E).obj P).homology i :=
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
        (((T.tensor.obj (DerivedCategory.Q.obj E)).mapIso eP).symm ≪≫
          T.comparison E P hE hPKF) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app ((tensorLeft E).obj P)
  exact ⟨fun h => h.of_iso iso.symm, fun h => h.of_iso iso⟩

/-- The same statement at an arbitrary complex `X`: replace `X` by a K-flat resolution, which
changes neither side, since `P` is K-flat so tensoring by it inverts quasi-isomorphisms. -/
private theorem isZero_derivedTensor_iff_tensorResolution
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (π : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)
    (hPLE : P.IsStrictlyLE m) (hPproj : ∀ n : ℤ, Projective (P.X n)) (hπ : QuasiIso π) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((T.tensor.obj (DerivedCategory.Q.obj X)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) ↔
      IsZero (((tensorLeft X).obj P).homology i) := by
  have := hPLE
  have hPKF : P.KFlat := kFlat_of_isStrictlyLE_projective P m hPproj
  obtain ⟨G, p, hGlarge, -, hp, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} X
  have hG : G.KFlat := hGlarge
  have := hp
  have hq : QuasiIso ((tensorRight P).map p) := quasiIso_tensorRight_map hPKF p
  have := hq
  have eL : ((tensorLeft G).obj P).homology i ≅ ((tensorLeft X).obj P).homology i :=
    have : IsIso (HomologicalComplex.homologyMap ((tensorRight P).map p) i) :=
      (quasiIsoAt_iff_isIso_homologyMap _ i).mp (hq.quasiIsoAt i)
    asIso (HomologicalComplex.homologyMap ((tensorRight P).map p) i)
  have eD : (T.tensor.obj (DerivedCategory.Q.obj G)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ≅
      (T.tensor.obj (DerivedCategory.Q.obj X)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) :=
    (T.tensor.mapIso (asIso (DerivedCategory.Q.map p))).app _
  rw [← eL.isZero_iff,
    ← isZero_derivedTensor_iff_tensorResolution_of_kFlat T G hG M P m π hPLE hPproj hπ i,
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso eD).isZero_iff]

/-- The intermediate form of the Tor-amplitude condition used below: for every module `M` and
every bounded above resolution `P ⟶ M[0]` of it by projective modules, the cohomology of `X ⊗ P`
vanishes outside `[a, b]`.

The resolution is quantified over rather than chosen, because the projection formula that carries
the condition across a ring map produces the resolution it is applied to. -/
private def HasResolvedTorAmplitude (X : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) : Prop :=
  ∀ (M : ModuleCat.{u} R) (P : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    (π : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M),
    P.IsStrictlyLE m → (∀ n : ℤ, Projective (P.X n)) → QuasiIso π →
      ∀ i : ℤ, (i < a ∨ b < i) → IsZero (((tensorLeft X).obj P).homology i)

/-- Tor amplitude against a certified derived tensor bifunctor is the resolution-computed
condition. -/
private lemma hasTorAmplitudeIn_iff_resolved
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct R)
    (X : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified T)
      (DerivedCategory.Q.obj X) a b ↔
      HasResolvedTorAmplitude X a b := by
  constructor
  · intro h M P m π hPLE hPproj hπ i hi
    exact (isZero_derivedTensor_iff_tensorResolution T X M P m π hPLE hPproj hπ i).mp (h M i hi)
  · intro h M i hi
    obtain ⟨P, m, π, hPLE, hPproj, hπ⟩ :=
      exists_projective_resolution ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) 0
    exact (isZero_derivedTensor_iff_tensorResolution T X M P m π hPLE hPproj hπ i).mpr
      (h M P m π hPLE hPproj hπ i hi)

end Certificate

/-! ### Cohomological support of the total complex of a bicomplex

This section is the formalized spectral sequence of a double complex: the total complex of a
bicomplex with columns supported in `[a, b]` and rows with cohomology in `[c, d]` has cohomology
in `[a + c, b + d]`.
-/

section Bicomplex

variable {C : Type u} [Category* C] [Abelian C]

/-- A bicomplex whose columns vanish outside `[a, b]` has, in each total degree, only finitely
many nonzero terms on the antidiagonal. -/
private lemma finite_antidiagonal_of_horizontal_bounds
    (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a b n : ℤ)
    (hlo : ∀ p, p < a → IsZero (Z.X p)) (hhi : ∀ p, b < p → IsZero (Z.X p)) :
    {pq : ℤ × ℤ | ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) pq = n ∧ ¬ IsZero ((Z.X pq.1).X pq.2)}.Finite := by
  refine Set.Finite.subset ((Set.finite_Icc a b).image (fun p => (p, n - p))) ?_
  rintro ⟨p, q⟩ ⟨hpq, hz⟩
  have hpq' : p + q = n := hpq
  have hv : IsZero (Z.X p) → False := fun h =>
    hz (Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) q) h)
  have hpa : a ≤ p := by
    by_contra h
    exact hv (hlo p (by omega))
  have hpb : p ≤ b := by
    by_contra h
    exact hv (hhi p (by omega))
  refine ⟨p, ⟨hpa, hpb⟩, ?_⟩
  have hq : n - p = q := by omega
  simp [hq]

/-- A bicomplex whose columns vanish outside `[a, b]` has a total complex. -/
private lemma hasTotal_of_horizontal_bounds
    (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a b : ℤ)
    (hlo : ∀ p, p < a → IsZero (Z.X p)) (hhi : ∀ p, b < p → IsZero (Z.X p)) :
    Z.HasTotal (ComplexShape.up ℤ) :=
  HomologicalComplex₂.hasTotal_of_finite _ _
    (finite_antidiagonal_of_horizontal_bounds Z a b · hlo hhi)

/-- The total complex of the bicomplex with the single column `W` in position `a` is `W` shifted
by `-a`, so its cohomology starts in degree `a + c` when that of `W` starts in degree `c`. -/
private lemma singleColumn_isGE (W : CochainComplex C ℤ) (a c : ℤ) [W.IsGE c]
    [(StacksDraft.TotalComplexQuasiIso.singleColumn W a).HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.IsGE
      ((StacksDraft.TotalComplexQuasiIso.singleColumn W a).total (ComplexShape.up ℤ)) (a + c) := by
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit W a
  have hs : (W⟦-a⟧).IsGE (a + c) := W.isGE_shift c (-a) (a + c) (by omega)
  have := hs
  exact CochainComplex.isGE_of_iso
    (asIso (StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit W a)) (a + c)

/-- Dually, the cohomology of the total complex of a single column in position `a` ends in degree
`a + d` when that of the column ends in degree `d`. -/
private lemma singleColumn_isLE (W : CochainComplex C ℤ) (a d : ℤ) [W.IsLE d]
    [(StacksDraft.TotalComplexQuasiIso.singleColumn W a).HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.IsLE
      ((StacksDraft.TotalComplexQuasiIso.singleColumn W a).total (ComplexShape.up ℤ)) (a + d) := by
  have := StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit W a
  have hs : (W⟦-a⟧).IsLE (a + d) := W.isLE_shift d (-a) (a + d) (by omega)
  have := hs
  exact CochainComplex.isLE_of_iso
    (asIso (StacksDraft.TotalComplexQuasiIso.totalSingleColumnUnit W a)) (a + d)

/-- In a short exact sequence of complexes, a lower bound on the cohomology of the outer terms is
a lower bound on the cohomology of the middle term. -/
private lemma middle_isGE_of_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n : ℤ) [S.X₁.IsGE n] [S.X₃.IsGE n] : S.X₂.IsGE n := by
  rw [CochainComplex.isGE_iff]
  intro i hi
  exact hS.exactAt_X₂ i (S.X₁.exactAt_of_isGE n i hi) (S.X₃.exactAt_of_isGE n i hi)

/-- In a short exact sequence of complexes, an upper bound on the cohomology of the outer terms is
an upper bound on the cohomology of the middle term. -/
private lemma middle_isLE_of_shortExact (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n : ℤ) [S.X₁.IsLE n] [S.X₃.IsLE n] : S.X₂.IsLE n := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  exact hS.exactAt_X₂ i (S.X₁.exactAt_of_isLE n i hi) (S.X₃.exactAt_of_isLE n i hi)

/-- The total complex of a bicomplex all of whose columns vanish vanishes degreewise. -/
private lemma isZero_total_X_of_zero_columns
    (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ))
    [Z.HasTotal (ComplexShape.up ℤ)] (h : ∀ p, IsZero (Z.X p)) (n : ℤ) :
    IsZero ((Z.total (ComplexShape.up ℤ)).X n) := by
  refine StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
    (Z.toGradedObject.isColimitCofanMapObj _ n) (fun i => ?_)
  obtain ⟨⟨p, q⟩, hpq⟩ := i
  exact Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) q) (h p)

/-- A complex all of whose terms vanish has cohomology in every interval. -/
private lemma isGE_and_isLE_of_isZero_X (W : CochainComplex C ℤ) (h : ∀ i, IsZero (W.X i))
    (s t : ℤ) : W.IsGE s ∧ W.IsLE t := by
  constructor
  · rw [CochainComplex.isGE_iff]
    exact fun i _ => HomologicalComplex.ExactAt.of_isZero (h i)
  · rw [CochainComplex.isLE_iff]
    exact fun i _ => HomologicalComplex.ExactAt.of_isZero (h i)

/-- If `b < a`, a bicomplex whose columns vanish outside `[a, b]` has vanishing columns, hence its
total complex has cohomology in every interval. -/
private lemma total_support_of_empty_range
    (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a b c d : ℤ)
    [Z.HasTotal (ComplexShape.up ℤ)] (hab : b < a)
    (hlo : ∀ p, p < a → IsZero (Z.X p)) (hhi : ∀ p, b < p → IsZero (Z.X p)) :
    CochainComplex.IsGE (Z.total (ComplexShape.up ℤ)) (a + c) ∧
      CochainComplex.IsLE (Z.total (ComplexShape.up ℤ)) (b + d) :=
  isGE_and_isLE_of_isZero_X _ (isZero_total_X_of_zero_columns Z fun p => by
    by_cases hp : p < a
    · exact hlo p hp
    · exact hhi p (by omega)) _ _

/-- **The spectral sequence of a double complex, by induction on the number of columns.** If the
columns of `Z` vanish outside `[a, b]` and every column has cohomology in `[c, d]`, then the total
complex of `Z` has cohomology in `[a + c, b + d]`.

The induction splits off the column in position `a` by the short exact sequence of total complexes
attached to the surjection of `Z` onto that column, whose kernel has its columns supported in
`[a + 1, b]`. -/
private lemma total_support_aux (k : ℕ) :
    ∀ (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a b c d : ℤ),
      (b - a + 1).toNat ≤ k →
      (∀ p, p < a → IsZero (Z.X p)) →
      (∀ p, b < p → IsZero (Z.X p)) →
      (∀ p, CochainComplex.IsGE (Z.X p) c ∧ CochainComplex.IsLE (Z.X p) d) →
      ∀ [Z.HasTotal (ComplexShape.up ℤ)],
        CochainComplex.IsGE (Z.total (ComplexShape.up ℤ)) (a + c) ∧
          CochainComplex.IsLE (Z.total (ComplexShape.up ℤ)) (b + d) := by
  induction k with
  | zero =>
    intro Z a b c d hk hlo hhi _ _
    exact total_support_of_empty_range Z a b c d (by omega) hlo hhi
  | succ k ih =>
    intro Z a b c d hk hlo hhi hrow _
    by_cases hab : b < a
    · exact total_support_of_empty_range Z a b c d hab hlo hhi
    have hZa : IsZero (Z.X (a - 1)) := hlo _ (by omega)
    let Z' := kernel (StacksDraft.TotalComplexQuasiIso.bottomProj Z a hZa)
    have hlo' : ∀ p, p < a + 1 → IsZero (Z'.X p) :=
      StacksDraft.TotalComplexQuasiIso.isZero_bottomTrunc_X a hZa hlo
    have hhi' : ∀ p, b < p → IsZero (Z'.X p) := by
      intro p hp
      exact StacksDraft.TotalComplexQuasiIso.isZero_kernel_bottomProj_X Z a hZa p (hhi p hp)
    have hrow' : ∀ p, CochainComplex.IsGE (Z'.X p) c ∧ CochainComplex.IsLE (Z'.X p) d := by
      intro p
      by_cases hp : p = a
      · subst hp
        have hz : IsZero (Z'.X p) :=
          StacksDraft.TotalComplexQuasiIso.isZero_kernel_bottomProj_X_self Z p hZa
        have hz' (i : ℤ) : IsZero ((Z'.X p).X i) :=
          Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) i) hz
        exact isGE_and_isLE_of_isZero_X _ hz' c d
      · have hi := StacksDraft.TotalComplexQuasiIso.isIso_kernel_ι_bottomProj_f Z a hZa p hp
        have := hi
        let e : Z'.X p ≅ Z.X p :=
          asIso ((kernel.ι (StacksDraft.TotalComplexQuasiIso.bottomProj Z a hZa)).f p)
        have : CochainComplex.IsGE (Z.X p) c := (hrow p).1
        have : CochainComplex.IsLE (Z.X p) d := (hrow p).2
        exact ⟨CochainComplex.isGE_of_iso e.symm c, CochainComplex.isLE_of_iso e.symm d⟩
    have : Z'.HasTotal (ComplexShape.up ℤ) :=
      hasTotal_of_horizontal_bounds Z' (a + 1) b hlo' hhi'
    have : (StacksDraft.TotalComplexQuasiIso.singleColumn (Z.X a) a).HasTotal
        (ComplexShape.up ℤ) :=
      StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn (Z.X a) a
    have hrec := ih Z' (a + 1) b c d (by omega) hlo' hhi' hrow'
    have : CochainComplex.IsGE (Z.X a) c := (hrow a).1
    have : CochainComplex.IsLE (Z.X a) d := (hrow a).2
    have hrightGE := singleColumn_isGE (Z.X a) a c
    have hrightLE := singleColumn_isLE (Z.X a) a d
    have hleftGE : CochainComplex.IsGE (Z'.total (ComplexShape.up ℤ)) (a + c) := by
      have : CochainComplex.IsGE (Z'.total (ComplexShape.up ℤ)) (a + 1 + c) := hrec.1
      exact CochainComplex.isGE_of_ge (Z'.total (ComplexShape.up ℤ)) (a + c) (a + 1 + c) (by omega)
    have hrightLE' : CochainComplex.IsLE
        ((StacksDraft.TotalComplexQuasiIso.singleColumn (Z.X a) a).total
          (ComplexShape.up ℤ)) (b + d) := by
      have := hrightLE
      exact CochainComplex.isLE_of_le
        ((StacksDraft.TotalComplexQuasiIso.singleColumn (Z.X a) a).total
          (ComplexShape.up ℤ)) (a + d) (b + d) (by omega)
    have hS := StacksDraft.TotalComplexQuasiIso.totalBottomSES_shortExact Z a hZa
    constructor
    · have : (StacksDraft.TotalComplexQuasiIso.totalBottomSES Z a hZa).X₁.IsGE (a + c) := hleftGE
      have : (StacksDraft.TotalComplexQuasiIso.totalBottomSES Z a hZa).X₃.IsGE (a + c) := hrightGE
      exact middle_isGE_of_shortExact _ hS (a + c)
    · have : (StacksDraft.TotalComplexQuasiIso.totalBottomSES Z a hZa).X₁.IsLE (b + d) := hrec.2
      have : (StacksDraft.TotalComplexQuasiIso.totalBottomSES Z a hZa).X₃.IsLE (b + d) :=
        hrightLE'
      exact middle_isLE_of_shortExact _ hS (b + d)

/-- `total_support_aux` with the induction parameter discharged. -/
private lemma total_support_of_horizontal_bounds
    (Z : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)) (a b c d : ℤ)
    (hlo : ∀ p, p < a → IsZero (Z.X p)) (hhi : ∀ p, b < p → IsZero (Z.X p))
    (hrow : ∀ p, CochainComplex.IsGE (Z.X p) c ∧ CochainComplex.IsLE (Z.X p) d)
    [Z.HasTotal (ComplexShape.up ℤ)] :
    CochainComplex.IsGE (Z.total (ComplexShape.up ℤ)) (a + c) ∧
      CochainComplex.IsLE (Z.total (ComplexShape.up ℤ)) (b + d) :=
  total_support_aux (b - a + 1).toNat Z a b c d le_rfl hlo hhi hrow

/-- A complex all of whose terms vanish is a zero object. -/
private lemma isZero_complex_of_zero_components {D : Type u} [Category* D] [Preadditive D]
    (W : CochainComplex D ℤ) (h : ∀ i, IsZero (W.X i)) : IsZero W := by
  rw [IsZero.iff_id_eq_zero]
  ext i
  exact (h i).eq_of_src _ _

end Bicomplex

/-- **The tensor product of a bounded complex of flats with a cohomologically bounded complex.**
If `E` is a complex of flat `B`-modules vanishing outside `[a, b]` and `W` has cohomology in
`[c, d]`, then `E ⊗ W` has cohomology in `[a + c, b + d]`.

The columns of the bicomplex `E ⊗ W` are `E^p ⊗ W`, and `E^p ⊗ -` is exact, so each column has the
cohomology of `W`. -/
private lemma flat_tensor_bicomplex_support (B : Type u) [CommRing B]
    (E W : CochainComplex (ModuleCat.{u} B) ℤ) (a b c d : ℤ)
    (hlo : ∀ p, p < a → IsZero (E.X p)) (hhi : ∀ p, b < p → IsZero (E.X p))
    (hflat : ∀ p, Module.Flat B (E.X p)) [W.IsGE c] [W.IsLE d] :
    let Z := (((curriedTensor (ModuleCat.{u} B)).mapBifunctorHomologicalComplex
      (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj E).obj W
    CochainComplex.IsGE (Z.total (ComplexShape.up ℤ)) (a + c) ∧
      CochainComplex.IsLE (Z.total (ComplexShape.up ℤ)) (b + d) := by
  dsimp only
  let Z := (((curriedTensor (ModuleCat.{u} B)).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj E).obj W
  have hzero (p : ℤ) (hp : IsZero (E.X p)) : IsZero (Z.X p) := by
    apply isZero_complex_of_zero_components
    intro q
    change IsZero ((E.X p) ⊗ (W.X q))
    exact Functor.map_isZero ((curriedTensor (ModuleCat.{u} B)).flip.obj (W.X q)) hp
  have hrow (p : ℤ) : CochainComplex.IsGE (Z.X p) c ∧ CochainComplex.IsLE (Z.X p) d := by
    have : Module.Flat B (E.X p) := hflat p
    let F := tensorLeft (E.X p)
    have hF : F.PreservesHomology := Functor.preservesHomologyOfExact F
    constructor
    · change CochainComplex.IsGE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) c
      rw [CochainComplex.isGE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff]
      exact (W.exactAt_of_isGE c i hi).map F
    · change CochainComplex.IsLE ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj W) d
      rw [CochainComplex.isLE_iff]
      intro i hi
      rw [HomologicalComplex.exactAt_iff]
      exact (W.exactAt_of_isLE d i hi).map F
  have : Z.HasTotal (ComplexShape.up ℤ) :=
    hasTotal_of_horizontal_bounds Z a b (fun p hp => hzero p (hlo p hp))
      (fun p hp => hzero p (hhi p hp))
  exact total_support_of_horizontal_bounds Z a b c d (fun p hp => hzero p (hlo p hp))
    (fun p hp => hzero p (hhi p hp)) hrow

/-! ### The projection formula, in the form used here -/

section Projection

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

set_option maxHeartbeats 1000000 in
-- Elaborating the two nested `mapHomologicalComplex` layers of the projection-formula iso against
-- the short complex of the tensor product is slow.
/-- **The projection formula on cohomology.** For a complex `K` of `B`-modules and a complex `P` of
`A`-modules, the degree-`i` cohomology of `K ⊗_B (B ⊗_A P)`, restricted to `A`, is the degree-`i`
cohomology of `(restrict K) ⊗_A P`.

This is `StacksDraft.TorAmplitude.FaithfullyFlat.restrictTensorLeftExtendIso` on cohomology,
exactly as `StacksDraft.TorAmplitude.FaithfullyFlat.derivedTensorHomologyARestrictIso` uses it,
but for an arbitrary complex `P` in place of the chosen projective resolution of a module. -/
private noncomputable def restrictTensorExtendHomologyIso
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (P : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (ModuleCat.restrictScalars (algebraMap A B)).obj
        (((tensorLeft K).obj
          ((CochainComplex.extendScalars (algebraMap A B)).obj P)).homology i) ≅
      ((tensorLeft ((CochainComplex.restrictScalars (algebraMap A B)).obj K)).obj P).homology i :=
  (ShortComplex.mapHomologyIso
      (((tensorLeft K).obj ((CochainComplex.extendScalars (algebraMap A B)).obj P)).sc i)
      (ModuleCat.restrictScalars (algebraMap A B))).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso
      (StacksDraft.TorAmplitude.FaithfullyFlat.restrictTensorLeftExtendIso A B K P)

/-- **The core of Stacks 0B66 at the level of ordinary complexes.** Let `E` be a complex of flat
`B`-modules vanishing outside `[a, b]` and let `F` be a complex of `B`-modules whose restriction to
`A` satisfies the resolution-computed Tor-amplitude condition for `[c, d]`. Then the restriction of
`E ⊗ F` to `A` satisfies it for `[a + c, b + d]`.

Given a resolution `P ⟶ M[0]` of an `A`-module, the projection formula turns the hypothesis on `F`
into cohomological bounds `[c, d]` for `W = F ⊗_B (B ⊗_A P)`, the double-complex bound gives
`E ⊗ W` cohomology in `[a + c, b + d]`, the associator identifies `E ⊗ W` with
`(E ⊗ F) ⊗_B (B ⊗_A P)`, and the projection formula in the other direction gives the
conclusion. -/
private lemma resolved_tensor_restricted (E F : CochainComplex (ModuleCat.{u} B) ℤ) (a b c d : ℤ)
    (hElo : ∀ p, p < a → IsZero (E.X p)) (hEhi : ∀ p, b < p → IsZero (E.X p))
    (hflat : ∀ p, Module.Flat B (E.X p))
    (hF : HasResolvedTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A B)).obj F) c d) :
    HasResolvedTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A B)).obj (E ⊗ F)) (a + c) (b + d) := by
  intro M P m π hPLE hPproj hπ i hi
  set V := (CochainComplex.extendScalars (algebraMap A B)).obj P with hV
  set W := (tensorLeft F).obj V with hW
  have hWz : ∀ j : ℤ, (j < c ∨ d < j) → IsZero (W.homology j) := by
    intro j hj
    rw [← StacksDraft.TorAmplitude.FaithfullyFlat.isZero_restrictScalars_iff
      (algebraMap A B) (W.homology j)]
    exact (hF M P m π hPLE hPproj hπ j hj).of_iso (restrictTensorExtendHomologyIso A B F P j)
  have hWGE : W.IsGE c := by
    rw [CochainComplex.isGE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hWz j (Or.inl hj)
  have hWLE : W.IsLE d := by
    rw [CochainComplex.isLE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hWz j (Or.inr hj)
  have := hWGE
  have := hWLE
  have hEW := flat_tensor_bicomplex_support B E W a b c d hElo hEhi hflat
  have hz : IsZero ((E ⊗ W).homology i) := by
    rcases hi with hi | hi
    · have : CochainComplex.IsGE (E ⊗ W) (a + c) := hEW.1
      exact (E ⊗ W).isZero_of_isGE (a + c) i hi
    · have : CochainComplex.IsLE (E ⊗ W) (b + d) := hEW.2
      exact (E ⊗ W).isZero_of_isLE (b + d) i hi
  have hz' : IsZero (((E ⊗ F) ⊗ V).homology i) :=
    hz.of_iso ((HomologicalComplex.homologyFunctor _ _ i).mapIso (α_ E F V))
  exact (Functor.map_isZero (ModuleCat.restrictScalars (algebraMap A B)) hz').of_iso
    (restrictTensorExtendHomologyIso A B (E ⊗ F) P i).symm

end Projection

/-! ### Stacks 0B66 -/

section Main

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- **Stacks 0B66.** Let `A → B` be a map of commutative rings and let `K` and `L` be complexes of
`B`-modules. If `K` has Tor amplitude in `[a, b]` as a complex of `B`-modules, and `L` has Tor
amplitude in `[c, d]` as a complex of `A`-modules, then `K ⊗_B^L L` has Tor amplitude in
`[a + c, b + d]` as a complex of `A`-modules.

The derived tensor products over `A` and over `B` are certified bifunctors in the sense of Stacks
064M and 0BYI; see the module docstring for why the certified triple of Stacks 0652 does not
suffice to state this. Over `B` the 0652 certificate is assumed in addition, and is used exactly
once, to apply Stacks 0654 to `K`.

This is **not** the 0B66 endpoint: it is quantified over an arbitrary certified bifunctor over
each of `A` and `B`, whereas the source states 0B66 at the *canonical* derived tensor product of
Stacks 0BYI, and a `∀`-quantified statement asserts nothing at the canonical datum until that
datum is produced. It is the arbitrary-certificate helper from which the endpoint
`hasTorAmplitudeCanonical_derivedTensorProduct` of
`StacksFrontier.Homology.TorAmplitude.CompositionCanonical` is obtained by instantiation at the
certificate of `StacksFrontier.Homology.TorAmplitude.CanonicalCertificate`, and it carries no
`@[stacks]` attribute. -/
public theorem hasTorAmplitudeIn_derivedTensor
    (TA : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (TB : CochainComplex.DerivedTensor.DerivedTensorProduct B)
    (comparisonB : ∀ N : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ TB.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedB : ∀ N : ModuleCat.{u} B,
      (TB.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N)).IsLeftDerivedFunctor
          (comparisonB N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (K L : CochainComplex (ModuleCat.{u} B) ℤ) (a b c d : ℤ)
    (hK : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TB)
      (DerivedCategory.Q.obj K) a b)
    (hL : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj L)) c d) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        ((TB.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L)))
      (a + c) (b + d) := by
  obtain ⟨E, hEflat, hEGE, hELE, ⟨eK⟩⟩ :=
    (hasTorAmplitude_iff_hasFlatRepresentative comparisonB isLeftDerivedB
        (DerivedCategory.Q.obj K) a b).mp
      ((hasTorAmplitudeIn_iff_hasTorAmplitude TB comparisonB isLeftDerivedB _ a b).mp hK)
  have := hEGE
  have := hELE
  have hEflat' : ∀ n : ℤ, Module.Flat B (E.X n) := hEflat
  have := hEflat'
  have hEKF : E.KFlat :=
    (CochainComplex.KFlat.kFlat_of_flat E b)
  obtain ⟨F, q, hFlarge, -, hq, -⟩ := CochainComplex.KFlat.exists_kFlat_resolution.{u, u} L
  have hFKF : F.KFlat := hFlarge
  have := hq
  let eF : DerivedCategory.Q.obj F ≅ DerivedCategory.Q.obj L := asIso (DerivedCategory.Q.map q)
  let RD := (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory
  have hFres : HasResolvedTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap A B)).obj F) c d :=
    (hasTorAmplitudeIn_iff_resolved TA _ c d).mp
      (hasTorAmplitudeIn_of_iso _
        ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app F)
        (hasTorAmplitudeIn_of_iso _ (RD.mapIso eF.symm) hL))
  have hOrd' : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars (algebraMap A B)).obj (E ⊗ F)))
      (a + c) (b + d) :=
    (hasTorAmplitudeIn_iff_resolved TA _ (a + c) (b + d)).mpr
      (resolved_tensor_restricted A B E F a b c d
        (fun p hp => E.isZero_of_isStrictlyGE a p hp)
        (fun p hp => E.isZero_of_isStrictlyLE b p hp) hEflat hFres)
  let eTensor : (TB.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj (E ⊗ F) :=
    (TB.tensor.mapIso eK).app (DerivedCategory.Q.obj L) ≪≫
      (TB.tensor.obj (DerivedCategory.Q.obj E)).mapIso eF.symm ≪≫ TB.comparison E F hEKF hFKF
  exact hasTorAmplitudeIn_of_iso _
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategoryFactors.app
      (E ⊗ F)).symm ≪≫ RD.mapIso eTensor.symm) hOrd'

/-! ### Stacks 066K -/

/-- **Stacks 066K.** Let `A → B` be a map of commutative rings and assume that `B` has Tor
dimension at most `d` as an `A`-module, that is, that `B` placed in degree zero has Tor amplitude
in `[-d, 0]` over `A`. Then a complex `K` of `B`-modules with Tor amplitude in `[a, b]` over `B`
has Tor amplitude in `[a - d, b]` over `A`.

This is Stacks 0B66 with `L = B[0]`: the right unit of the certified derived tensor product
identifies `K ⊗_B^L B[0]` with `K`, and the two intervals `[a + (-d), b + 0]` and `[a - d, b]`
agree.

This is **not** the 066K endpoint, on two counts: it is quantified over an arbitrary certified
bifunctor over each of `A` and `B` where the source states 066K at the *canonical* derived tensor
product of Stacks 0BYI, and it pins the two rings and the carriers of the complex to one universe
where the source leaves all three independent and takes a plain ring map rather than an algebra
structure. It is the arbitrary-certificate, one-universe helper from which the endpoint
`hasTorAmplitudeCanonicalLift_restrictScalars_of_torDimensionLE` of
`StacksFrontier.Homology.TorAmplitude.CompositionCanonical` is obtained by instantiation at the
certificate of `StacksFrontier.Homology.TorAmplitude.CanonicalCertificate` followed by a lift of
both rings into the carriers' universe, and it carries no `@[stacks]` attribute. -/
public theorem hasTorAmplitudeIn_restrictScalars_of_torDimensionLE
    (TA : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (TB : CochainComplex.DerivedTensor.DerivedTensorProduct B)
    (comparisonB : ∀ N : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ TB.tensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerivedB : ∀ N : ModuleCat.{u} B,
      (TB.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj N)).IsLeftDerivedFunctor
          (comparisonB N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (a b d : ℤ)
    (hB : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        ((ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B))) (-d) 0)
    (hK : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TB)
      (DerivedCategory.Q.obj K) a b) :
    Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj K)) (a - d) b := by
  set L := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) with hLdef
  let RD := (ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory
  let eQL : (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B) ≅
      DerivedCategory.Q.obj L :=
    (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} B) 0).app (ModuleCat.of B B)
  have hL : Stacks.TorAmplitudeTriangle.HasTorAmplitudeIn (derivedTensoringOfCertified TA)
      (RD.obj (DerivedCategory.Q.obj L)) (-d) 0 :=
    hasTorAmplitudeIn_of_iso _
      ((((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategorySingleFunctor 0).app
        (ModuleCat.of B B)).symm ≪≫ RD.mapIso eQL) hB
  have h := hasTorAmplitudeIn_derivedTensor A B TA TB comparisonB isLeftDerivedB K L a b (-d) 0
    hK hL
  let eU : (TB.tensor.obj (DerivedCategory.Q.obj K)).obj (DerivedCategory.Q.obj L) ≅
      DerivedCategory.Q.obj K :=
    ((TB.tensor.obj (DerivedCategory.Q.obj K)).mapIso eQL).symm ≪≫
      TB.rightUnitor.app (DerivedCategory.Q.obj K)
  have h' := hasTorAmplitudeIn_of_iso _ (RD.mapIso eU) h
  simpa only [sub_eq_add_neg, add_zero] using h'

end Main

end

end StacksDraft.TorAmplitude
