module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.DerivedBounds
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QcqsQuasiCoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.BoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject

/-!
# Quasi-coherence of the unbounded derived direct image

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes. Then `Rf_*` carries
`D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)`: the cohomology sheaves of `Rf_* E` are quasi-coherent as soon
as those of `E` are.

The proof is the one in the source. Quasi-coherence is local on `S` and derived direct image
commutes with restriction to an open, so one may assume `S` affine, and in particular
quasi-compact; that reduction is
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_compactTarget`, and what is proved here
is the hypothesis it consumes. With `S` quasi-compact, three steps:

* On a module `M` placed in a single degree `n`, the cohomology `H^m(Rf_*(M[n]))` is the
  classical higher direct image `R^{m-n}f_* M`, quasi-coherent by [Stacks, Tag 01XJ], for
  `m ≥ n`; and zero for `m < n`, because `Rf_*` preserves a lower cohomological bound.
* On an object of `D(𝒪_X)` living in a bounded range of degrees, quasi-coherence follows by
  induction on the length of that range, splitting off one cohomology sheaf at a time with the
  canonical truncation triangle and using that the quasi-coherent modules form a weak Serre
  subcategory.
* An object bounded only below is handled by discarding what lies above the degree in question:
  `Rf_*(τ_{≥ b+1}E)` lies in degrees `≥ b + 1`, again because `Rf_*` preserves lower bounds, so
  `H^i(Rf_* E) = H^i(Rf_*(τ_{≤ b}E))` for `i ≤ b - 1`, and `τ_{≤ b}E` is bounded. A general
  object is handled by discarding what lies below: `Rf_*(τ_{≤ c}E)` lies in degrees `≤ c + N - 1`
  by [Stacks, Tag 08D5] part (2), so `H^i(Rf_* E) = H^i(Rf_*(τ_{≥ c+1}E))` once `c + N - 1 < i`,
  and `τ_{≥ c+1}E` is bounded below.

The last step is where part (2) enters, and it is the reason that part is stated for an
arbitrary upper bound `b` rather than for `b = 0`: the truncation `τ_{≤ c}E` whose image has to
be bounded moves with the degree `i` being tested.

## Main results

* `Stacks.SmallDerivedCategory.derivedCategoryB_obj_of_isGE_of_isLE`,
  `Stacks.SmallDerivedCategory.derivedCategoryB_obj_of_isGE` and
  `Stacks.SmallDerivedCategory.derivedCategoryB_obj_of_isLE_bound`: the three steps, for an
  arbitrary exact functor between unbounded derived categories, an arbitrary object property on
  the source and an arbitrary weak Serre subcategory of the target.
* `AlgebraicGeometry.isGE_derivedPushforward_obj_modules`: `Rf_*` preserves a lower
  cohomological bound.
* `AlgebraicGeometry.derivedCategoryB_derivedPushforward_of_compactSpace`: quasi-coherence of the
  cohomology sheaves of `Rf_* E` for a quasi-compact target.
* `AlgebraicGeometry.isQuasicoherent_derivedPushforward`: **[Stacks, Tag 08D5] part (1)**.

## Implementation notes

The three abstract steps are phrased with `DerivedCategoryB.derivedCategoryB Q` as the
conclusion, i.e. with quasi-coherence of *every* cohomology object, rather than degree by degree:
the triangle step of the induction is the five-term exact sequence of the weak Serre condition
and it needs three consecutive degrees of the two outer vertices at once.

Preservation of a lower bound by `Rf_*` is
`Stacks.SmallDerivedCategory.isGE_obj_of_isGE`, whose hypothesis — that the
structure map of the derived functor is invertible at the K-injective complexes — is
`isIso_derivedPushforwardUnit_app_of_isKInjective` of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces`, `Rf_*` being by construction computed by
K-injective resolutions.

The comparison of `H^m(Rf_*(M[n]))` with `R^{m-n}f_* M` is
`Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso`, at the degreewise pushforward
`RingedSpaceModuleAdjunction.modulePushforward f.toLRSHom.toShHom`. That functor is
`AlgebraicGeometry.Scheme.Modules.pushforward f` — the two spellings of the category of
`𝒪_X`-modules, and of pushforward along `f`, are definitionally equal — so [Stacks, Tag 01XJ] in
the shape `Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived` applies
to it directly.

`HasDerivedCategory.standard` is installed with a raised priority, not because another model is
wanted but because the import closure of
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre` carries the
locally small model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as a global instance,
and with the two in play at equal priority instance search no longer resolves
`HasDerivedCategory.{u + 1} X.Modules`. [Stacks, Tag 0D5W] and [Stacks, Tag 0BKJ], hence part (2),
are stated in the standard model, so that is the model here.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01LA](https://stacks.math.columbia.edu/tag/01LA)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward derivedPushforwardUnit
  isIso_derivedPushforwardUnit_app_of_isKInjective)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.SmallDerivedCategory

section WeakSerreCohomology

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]
  (R : DerivedCategory A ⥤ DerivedCategory B) [R.CommShift ℤ] [R.IsTriangulated]
  (P : ObjectProperty A) (hPiso : P.IsClosedUnderIsomorphisms) (hPzero : P.ContainsZero)
  (Q : ObjectProperty B) (hQ : WeakSerre.IsWeakSerre Q)
  (hSingle : ∀ M : A, P M → ∀ n : ℤ,
    DerivedCategoryB.derivedCategoryB Q (R.obj ((DerivedCategory.singleFunctor A n).obj M)))

omit [R.CommShift ℤ] [R.IsTriangulated] in
include hPiso hQ hSingle in
/-- An exact functor between unbounded derived categories carries an object concentrated in a
single degree, whose cohomology object satisfies `P`, to one all of whose cohomology objects lie
in the weak Serre subcategory `Q` — given that it does so on the objects `M[n]` for `M` in `P`.

An object with `E.IsGE b` and `E.IsLE b` is isomorphic to `H^b(E)[b]`, and `H^b(E)` satisfies `P`
by hypothesis. -/
theorem derivedCategoryB_obj_of_isGE_of_isLE_self (E : DerivedCategory A)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (b : ℤ) [E.IsGE b] [E.IsLE b] :
    DerivedCategoryB.derivedCategoryB Q (R.obj E) := by
  have := hPiso
  obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E b
  have hM : P M := P.prop_of_iso
    ((DerivedCategory.homologyFunctor A b).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A b).app M) (hE b)
  intro i
  exact hQ.isClosedUnderIsomorphisms.of_iso
    (((DerivedCategory.homologyFunctor B i).mapIso (R.mapIso e)).symm) (hSingle M hM b i)

include hPiso hPzero hQ hSingle in
/-- **The bounded step.** An exact functor between unbounded derived categories carries an object
living in a bounded range of degrees, all of whose cohomology objects satisfy `P`, to one all of
whose cohomology objects lie in the weak Serre subcategory `Q`.

The induction is on the length `b - a` of the range: the canonical truncation triangle
`τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` has a shorter first vertex and a third vertex concentrated in the
single degree `b`, and the middle vertex of the image triangle is controlled by the five-term
exact sequence of the weak Serre condition
(`DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished`). -/
theorem derivedCategoryB_obj_of_isGE_of_isLE (E : DerivedCategory A)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a b : ℤ) [E.IsGE a] [E.IsLE b] :
    DerivedCategoryB.derivedCategoryB Q (R.obj E) := by
  have := hPiso
  have := hPzero
  suffices h : ∀ (m : ℕ) (E : DerivedCategory A),
      (∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E)) →
      ∀ a b : ℤ, b < a + m → E.IsGE a → E.IsLE b →
        DerivedCategoryB.derivedCategoryB Q (R.obj E) from
    h (b - a + 1).toNat E hE a b (by omega) inferInstance inferInstance
  intro m
  induction m with
  | zero =>
      intro E hE a b hab _ _
      have hz : IsZero E := (IsZero.iff_id_eq_zero E).2
        (DerivedCategory.TStructure.t.zero (𝟙 E) b a (by omega))
      intro i
      exact DerivedCategoryB.zero_mem_of_isWeakSerre Q hQ _
        ((DerivedCategory.homologyFunctor B i).map_isZero (R.map_isZero hz))
  | succ m ih =>
      intro E hE a b hab hGE hLE
      let T := (DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E
      have ht : T ∈ distTriang (DerivedCategory A) :=
        DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E
      have hle₁ : T.obj₁.IsLE (b - 1) :=
        DerivedCategory.TStructure.t.isLE_truncLE_obj E (b - 1) (b - 1) le_rfl
      have hge₁ : T.obj₁.IsGE a :=
        inferInstanceAs (((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E).IsGE a)
      have hge₃ : T.obj₃.IsGE b := DerivedCategory.TStructure.t.isGE_truncGE_obj E b b le_rfl
      have hle₃ : T.obj₃.IsLE b :=
        inferInstanceAs (((DerivedCategory.TStructure.t.truncGE b).obj E).IsLE b)
      have h₁ := ih T.obj₁ (DerivedCategory.prop_homologyFunctor_truncLE_obj P E hE (b - 1))
        a (b - 1) (by omega) hge₁ hle₁
      have h₃ := derivedCategoryB_obj_of_isGE_of_isLE_self R P hPiso Q hQ hSingle T.obj₃
        (DerivedCategory.prop_homologyFunctor_truncGE_obj P E hE b) b
      exact DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished Q hQ
        (R.mapTriangle.obj T) (R.map_distinguished T ht) h₁ h₃

include hPiso hPzero hQ hSingle in
/-- **The bounded below step.** If in addition the functor preserves a lower cohomological bound,
it carries an object bounded below, all of whose cohomology objects satisfy `P`, to one all of
whose cohomology objects lie in `Q`.

Only finitely many degrees of `E` matter for a single degree `i` of the image: the image of
`τ_{≥ i+2}E` lies in degrees `≥ i + 2`, so the canonical truncation triangle at `i + 1` is
carried to one whose third vertex has no cohomology in degrees `i - 1` and `i`, and the long
exact sequence makes `H^i(R(τ_{≤ i+1}E)) ⟶ H^i(R E)` invertible. The truncation `τ_{≤ i+1}E` is
bounded. -/
theorem derivedCategoryB_obj_of_isGE
    (hGE : ∀ (K : DerivedCategory A) (c : ℤ), K.IsGE c → (R.obj K).IsGE c)
    (E : DerivedCategory A)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E))
    (a : ℤ) [E.IsGE a] :
    DerivedCategoryB.derivedCategoryB Q (R.obj E) := by
  have := hPiso
  have := hPzero
  intro i
  set b : ℤ := i + 1 with hb
  let T := (DerivedCategory.TStructure.t.triangleLEGE b (b + 1) rfl).obj E
  have ht : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.TStructure.t.triangleLEGE_distinguished b (b + 1) rfl E
  have hle₁ : T.obj₁.IsLE b := DerivedCategory.TStructure.t.isLE_truncLE_obj E b b le_rfl
  have hge₁ : T.obj₁.IsGE a :=
    inferInstanceAs (((DerivedCategory.TStructure.t.truncLE b).obj E).IsGE a)
  have hge₃ : (R.obj T.obj₃).IsGE (b + 1) :=
    hGE T.obj₃ (b + 1) (DerivedCategory.TStructure.t.isGE_truncGE_obj E (b + 1) (b + 1) le_rfl)
  have hz : IsZero ((DerivedCategory.homologyFunctor B i).obj (R.obj T.obj₃)) :=
    DerivedCategory.isZero_of_isGE _ (b + 1) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor B (i - 1)).obj (R.obj T.obj₃)) :=
    DerivedCategory.isZero_of_isGE _ (b + 1) (i - 1) (by omega)
  have hT : R.mapTriangle.obj T ∈ distTriang (DerivedCategory B) := R.map_distinguished T ht
  have hepi : Epi ((DerivedCategory.homologyFunctor B i).map (R.mapTriangle.obj T).mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₁_iff
      (R.mapTriangle.obj T) hT i).2 (hz.eq_of_tgt _ _)
  have hmono : Mono ((DerivedCategory.homologyFunctor B i).map (R.mapTriangle.obj T).mor₁) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₁_iff
      (R.mapTriangle.obj T) hT (i - 1) i (by omega)).2 (hz'.eq_of_src _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor B i).map
      (R.mapTriangle.obj T).mor₁) := isIso_of_mono_of_epi _
  have h₁ := derivedCategoryB_obj_of_isGE_of_isLE R P hPiso hPzero Q hQ hSingle T.obj₁
    (DerivedCategory.prop_homologyFunctor_truncLE_obj P E hE b) a b
  exact hQ.isClosedUnderIsomorphisms.of_iso (@asIso _ _ _ _ _ hiso) (h₁ i)

include hPiso hPzero hQ hSingle in
/-- **The general step.** If the functor preserves a lower cohomological bound and shifts an
upper one by at most a fixed amount `d` on the objects whose cohomology satisfies `P`, then it
carries every such object to one all of whose cohomology objects lie in `Q`.

For a single degree `i`, truncate below at `c = i - d - 1`: the image of `τ_{≤ c}E` lies in
degrees `≤ c + d = i - 1`, so the image of the truncation triangle has no cohomology in degrees
`i` and `i + 1` at its first vertex, and the long exact sequence makes
`H^i(R E) ⟶ H^i(R(τ_{≥ c+1}E))` invertible. The truncation `τ_{≥ c+1}E` is bounded below. -/
theorem derivedCategoryB_obj_of_isLE_bound
    (hGE : ∀ (K : DerivedCategory A) (c : ℤ), K.IsGE c → (R.obj K).IsGE c) (d : ℤ)
    (hLE : ∀ K : DerivedCategory A,
      (∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj K)) → ∀ c : ℤ, K.IsLE c →
        (R.obj K).IsLE (c + d))
    (E : DerivedCategory A)
    (hE : ∀ i : ℤ, P ((DerivedCategory.homologyFunctor A i).obj E)) :
    DerivedCategoryB.derivedCategoryB Q (R.obj E) := by
  have := hPiso
  have := hPzero
  intro i
  set c : ℤ := i - d - 1 with hc
  let T := (DerivedCategory.TStructure.t.triangleLEGE c (c + 1) rfl).obj E
  have ht : T ∈ distTriang (DerivedCategory A) :=
    DerivedCategory.TStructure.t.triangleLEGE_distinguished c (c + 1) rfl E
  have hle₁ : T.obj₁.IsLE c := DerivedCategory.TStructure.t.isLE_truncLE_obj E c c le_rfl
  have hge₃ : T.obj₃.IsGE (c + 1) :=
    DerivedCategory.TStructure.t.isGE_truncGE_obj E (c + 1) (c + 1) le_rfl
  have hb₁ : (R.obj T.obj₁).IsLE (c + d) :=
    hLE T.obj₁ (DerivedCategory.prop_homologyFunctor_truncLE_obj P E hE c) c hle₁
  have hz : IsZero ((DerivedCategory.homologyFunctor B i).obj (R.obj T.obj₁)) :=
    DerivedCategory.isZero_of_isLE _ (c + d) i (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor B (i + 1)).obj (R.obj T.obj₁)) :=
    DerivedCategory.isZero_of_isLE _ (c + d) (i + 1) (by omega)
  have hT : R.mapTriangle.obj T ∈ distTriang (DerivedCategory B) := R.map_distinguished T ht
  have hmono : Mono ((DerivedCategory.homologyFunctor B i).map (R.mapTriangle.obj T).mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_mono_shift_map_mor₂_iff
      (R.mapTriangle.obj T) hT i).2 (hz.eq_of_src _ _)
  have hepi : Epi ((DerivedCategory.homologyFunctor B i).map (R.mapTriangle.obj T).mor₂) :=
    ((DerivedCategory.homologyFunctor B 0).homologySequence_epi_shift_map_mor₂_iff
      (R.mapTriangle.obj T) hT i (i + 1) rfl).2 (hz'.eq_of_tgt _ _)
  have hiso : IsIso ((DerivedCategory.homologyFunctor B i).map
      (R.mapTriangle.obj T).mor₂) := isIso_of_mono_of_epi _
  have h₃ := derivedCategoryB_obj_of_isGE R P hPiso hPzero Q hQ hSingle hGE T.obj₃
    (DerivedCategory.prop_homologyFunctor_truncGE_obj P E hE (c + 1)) (c + 1)
  exact hQ.isClosedUnderIsomorphisms.of_iso (@asIso _ _ _ _ _ hiso).symm (h₃ i)

end WeakSerreCohomology

end Stacks.SmallDerivedCategory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The unbounded derived direct image preserves a lower cohomological bound.** If `E` lies in
degrees `≥ c` then so does `Rf_* E`, for an arbitrary morphism of schemes.

`Rf_*` is computed by K-injective resolutions, which is the hypothesis of
`Stacks.SmallDerivedCategory.isGE_obj_of_isGE`. -/
theorem isGE_derivedPushforward_obj_modules (E : DerivedCategory.{u + 1} X.Modules) (c : ℤ)
    (hE : E.IsGE c) : ((derivedPushforward f.toLRSHom.toShHom).obj E).IsGE c :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (isIso_derivedPushforwardUnit_app_of_isKInjective f.toLRSHom.toShHom) E c hE

/-- **The derived direct image of a quasi-coherent module placed in a single degree has
quasi-coherent cohomology.** For `f` quasi-compact and quasi-separated, every cohomology sheaf of
`Rf_*(M[n])` is quasi-coherent when `M` is.

In degrees `m ≥ n` this sheaf is the classical higher direct image `R^{m-n}f_* M`, quasi-coherent
by [Stacks, Tag 01XJ]; in degrees `m < n` it vanishes, `M[n]` lying in degrees `≥ n` and `Rf_*`
preserving that bound. -/
theorem derivedCategoryB_derivedPushforward_singleFunctor_obj [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) (hM : M.IsQuasicoherent) (n : ℤ) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules n).obj M)) := by
  have : M.IsQuasicoherent := hM
  intro m
  rcases le_or_gt n m with hnm | hnm
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m - n = (k : ℤ) :=
      ⟨(m - n).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
    exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso
      (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso
        (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
        (derivedPushforwardUnit f.toLRSHom.toShHom)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
          X.toRingedSpace) M n m k hk).symm
      (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.isQuasicoherent_rightDerived f M k)
  · have hge : ((derivedPushforward f.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor X.Modules n).obj M)).IsGE n :=
      isGE_derivedPushforward_obj_modules f _ n inferInstance
    exact DerivedCategoryB.zero_mem_of_isWeakSerre _
      (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S) _
      (DerivedCategory.isZero_of_isGE _ n m hnm (hX := hge))

/-- **Quasi-coherence of the cohomology sheaves of a derived direct image over a quasi-compact
base.** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. If every cohomology sheaf of `E` is quasi-coherent then so is every cohomology
sheaf of `Rf_* E`.

The three steps of
`Stacks.SmallDerivedCategory.derivedCategoryB_obj_of_isLE_bound` are fed: the single-degree case
is `derivedCategoryB_derivedPushforward_singleFunctor_obj`, the preservation of a lower bound is
`isGE_derivedPushforward_obj_modules`, and the upper bound with `d = N - 1` is [Stacks, Tag 08D5]
part (2) in the form `isZero_homology_derivedPushforward_of_isBasis`, whose basis and degree come
from [Stacks, Tag 01XJ]. Quasi-coherent modules form a weak Serre subcategory by
[Stacks, Tag 01LA]. -/
theorem derivedCategoryB_derivedPushforward_of_compactSpace [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] (E : DerivedCategory.{u + 1} X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((derivedPushforward f.toLRSHom.toShHom).obj E) := by
  obtain ⟨N, B, hB, hvan⟩ := exists_isBasis_isZero_rightDerivedPlus_sectionsOnPreimage f
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))
      (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
    (modulePushforward f.toLRSHom.toShHom) (derivedPushforward f.toLRSHom.toShHom)
    (derivedPushforwardUnit f.toLRSHom.toShHom)
  exact Stacks.SmallDerivedCategory.derivedCategoryB_obj_of_isLE_bound
    (derivedPushforward f.toLRSHom.toShHom)
    (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (isQuasicoherentModules_isClosedUnderIsomorphisms X) (isQuasicoherentModules_containsZero X)
    (SheafOfModules.isQuasicoherent S.ringCatSheaf)
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S)
    (fun M hM n ↦ derivedCategoryB_derivedPushforward_singleFunctor_obj f M hM n)
    (fun K c hK ↦ isGE_derivedPushforward_obj_modules f K c hK) ((N : ℤ) - 1)
    (fun K hK c hc ↦ (DerivedCategory.isLE_iff _ _).2 fun m hm ↦
      isZero_homology_derivedPushforward_of_isBasis f hB hvan K hK c hc m (by omega))
    E hE

/-- **Stacks 08D5, part (1).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of
schemes. The unbounded derived direct image `Rf_*` carries `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_S)`: the
cohomology sheaves of `Rf_* E` are quasi-coherent for every object `E` of `D(𝒪_X)` whose
cohomology sheaves are.

Quasi-coherence is local on the target and `Rf_*` commutes with restriction to an open, which is
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_compactTarget`; the affine case is
`preservesQuasicoherentOnCompactTarget`. -/
@[stacks 08D5 "quasi_coherent_direct_image"]
theorem isQuasicoherent_derivedPushforward [QuasiCompact f] [QuasiSeparated f]
    (E : QuasicoherentDerivedCategory X) :
    DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf)
      ((RingedSpace.derivedPushforward f.toLRSHom.toShHom).obj E.obj) :=
  isQuasicoherent_derivedPushforward_of_compactTarget preservesQuasicoherentOnCompactTarget f E

end AlgebraicGeometry

end
