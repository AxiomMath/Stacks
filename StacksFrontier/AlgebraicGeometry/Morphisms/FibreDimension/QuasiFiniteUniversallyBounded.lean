module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteFactorization

/-!
# A quasi-finite morphism with quasi-compact source has universally bounded fibres

A locally quasi-finite morphism of finite type whose source is quasi-compact has universally
bounded fibres.

## Main results

* `AlgebraicGeometry.finrank_le_of_surjective_appTop` transfers a bound on the dimension of the
  global sections of a scheme over a field to a scheme mapping into it by a morphism that is
  surjective on global sections.
* `AlgebraicGeometry.isAffine_and_finrank_le_of_isOpenImmersion`: an open subscheme of an affine
  scheme whose global sections are finite dimensional over a field is affine and its global
  sections have no larger dimension.
* `AlgebraicGeometry.finrank_le_sum_of_openCover` bounds the dimension of the global sections of
  a scheme over a field by the sum of the bounds on the members of a finite open cover.
* `AlgebraicGeometry.finrank_le_of_isPullback_of_isFinite` bounds the dimension of the global
  sections of a field-valued base change of a finite morphism of affine schemes by the number of
  module generators of the source.
* `AlgebraicGeometry.exists_finrank_fibre_bound_of_affine_pair`: for a pair of affine opens `U`
  of the source and `V` of the target with `f '' U ⊆ V`, the global sections of every
  field-valued base change of `U.ι ≫ f` are finite dimensional of dimension bounded
  independently of the base change.
* `AlgebraicGeometry.boundsFiberDegrees_of_openCover_of_finrank_le` turns such bounds on the
  members of a finite open cover of the source into a bound on the degrees of the fibres.  It is
  the finrank-data form; `AlgebraicGeometry.boundsFiberDegrees_of_openCover` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresOpenCover` is the
  statement whose hypothesis is a degree bound on each member, and neither hypothesis implies
  the other.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite` is Tag 03JA.

## Implementation notes

Following the convention of Tag 01TD recorded in
`StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/Defs.lean`, "`f` is quasi-finite" is
expressed by the two typeclasses `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`; quasi-compactness of the source is `CompactSpace`.

The argument is carried out in terms of the dimension of the ring of global sections of a fibre
over the residue field, not in terms of the rank of Tag 03J4 itself. The two are interchangeable
over a field — `Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis` produces the rank from a
basis of the global sections — and only the production is needed, at the very last step. Working
with dimensions makes the two composition steps of the proof elementary: the dimension is
monotone along a morphism that is surjective on global sections, and subadditive along a finite
open cover.

That a fibre is a *finite* scheme over the residue field is not assumed but derived: once its
global sections are known to be finite dimensional over the residue field, the fibre is
quasi-compact, and `AlgebraicGeometry.IsFinite.of_locallyQuasiFinite` applies because the
spectrum of a field is Artinian.

The one place an open immersion has to be turned into a closed immersion is
`AlgebraicGeometry.isAffine_and_finrank_le_of_isOpenImmersion`: an affine scheme whose global
sections are a finite dimensional algebra over a field is Artinian, hence discrete, so every
subset of it is closed and an open immersion into it is a closed immersion. This is what makes
the restriction of a fibre to an open chart cost nothing in dimension, and it is why the general
composition law for bounded fibre degrees (Tag 03J6) is not needed here.

## References

* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03GU](https://stacks.math.columbia.edu/tag/03GU)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace AlgebraicGeometry

/-- A pullback square whose right-hand leg is composed with a monomorphism on both sides is
again a pullback square. This holds in any category; it is stated here because that is where it
is used. -/
theorem isPullback_comp_mono {C : Type*} [Category C] {P T V Y S : C} {a : P ⟶ T} {b : P ⟶ S}
    {π : T ⟶ V} {c : S ⟶ V} (h : IsPullback a b π c) (v : V ⟶ Y) [Mono v] :
    IsPullback a b (π ≫ v) (c ≫ v) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (W := P) (by
    rw [← Category.assoc, ← Category.assoc, h.w])
    (fun s => h.lift s.fst s.snd
      ((cancel_mono v).mp (by simpa only [Category.assoc] using s.condition)))
    (fun _ => h.lift_fst _ _ _) (fun _ => h.lift_snd _ _ _)
    (fun _ _ h₁ h₂ => h.hom_ext (by rw [h₁, h.lift_fst]) (by rw [h₂, h.lift_snd])))

/-- Precomposition with a morphism carries the algebra structure that a morphism to the spectrum
of a ring puts on the global sections of its source to the one its composite puts there. -/
theorem appTop_algebraMap_comp {K : Type u} [Field K] {Z Z' : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (ι : Z' ⟶ Z) :
    letI : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra K ↑Γ(Z', ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom.toAlgebra
    ∀ a : K, ι.appTop.hom (algebraMap K ↑Γ(Z, ⊤) a) = algebraMap K ↑Γ(Z', ⊤) a := by
  intro a
  show (((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop) ≫ ι.appTop).hom _ =
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom _
  rw [Scheme.Hom.comp_appTop, Category.assoc]

/-- Precomposition with `ι` as a linear map between the global sections, which are algebras over a
field in the base. -/
private noncomputable def appTopLinearMap {K : Type u} [Field K] {Z Z' : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (ι : Z' ⟶ Z) :
    letI : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra K ↑Γ(Z', ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom.toAlgebra
    ↑Γ(Z, ⊤) →ₗ[K] ↑Γ(Z', ⊤) := by
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra K ↑Γ(Z', ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom.toAlgebra
  exact (AlgHom.mk (ι.appTop.hom : _ →+* _) (appTop_algebraMap_comp p ι)).toLinearMap

/-- A morphism that is surjective on global sections does not increase the dimension of the
global sections over a field in the base. -/
theorem finrank_le_of_surjective_appTop {K : Type u} [Field K] {Z Z' : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (ι : Z' ⟶ Z) (hι : Function.Surjective ι.appTop.hom) (n : ℕ)
    (h : letI : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
      Module.Finite K ↑Γ(Z, ⊤) ∧ Module.finrank K ↑Γ(Z, ⊤) ≤ n) :
    letI : Algebra K ↑Γ(Z', ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom.toAlgebra
    Module.Finite K ↑Γ(Z', ⊤) ∧ Module.finrank K ↑Γ(Z', ⊤) ≤ n := by
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra K ↑Γ(Z', ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom.toAlgebra
  obtain ⟨hfin, hle⟩ := h
  let L := appTopLinearMap p ι
  have hLsurj : Function.Surjective L := hι
  refine ⟨Module.Finite.of_surjective L hLsurj, ?_⟩
  calc Module.finrank K ↑Γ(Z', ⊤) ≤ Module.finrank K ↑Γ(Z, ⊤) := by
        have hr := LinearMap.finrank_range_le L
        rwa [LinearMap.range_eq_top.mpr hLsurj, finrank_top] at hr
    _ ≤ n := hle

/-- An open subscheme of an affine scheme whose global sections are a finite dimensional algebra
over a field in the base is affine, and its global sections have no larger dimension.

The affine scheme is Artinian, hence discrete, so the open immersion is also a closed immersion
and is therefore surjective on global sections. -/
theorem isAffine_and_finrank_le_of_isOpenImmersion {K : Type u} [Field K] {Z Z' : Scheme.{u}}
    [IsAffine Z] (p : Z ⟶ Spec (.of K)) (ι : Z' ⟶ Z) [IsOpenImmersion ι] (n : ℕ)
    (h : letI : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
      Module.Finite K ↑Γ(Z, ⊤) ∧ Module.finrank K ↑Γ(Z, ⊤) ≤ n) :
    IsAffine Z' ∧
      letI : Algebra K ↑Γ(Z', ⊤) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ (ι ≫ p).appTop).hom.toAlgebra
      Module.Finite K ↑Γ(Z', ⊤) ∧ Module.finrank K ↑Γ(Z', ⊤) ≤ n := by
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  have hfin : Module.Finite K ↑Γ(Z, ⊤) := h.1
  have : IsArtinianRing ↑Γ(Z, ⊤) := IsArtinianRing.of_finite K ↑Γ(Z, ⊤)
  have : IsLocallyArtinian Z := IsLocallyArtinian.of_isImmersion Z.isoSpec.hom
  have : IsClosedImmersion ι := IsClosedImmersion.of_isPreimmersion ι (isClosed_discrete _)
  exact ⟨isAffine_of_isAffineHom ι, finrank_le_of_surjective_appTop p ι
    (Scheme.Hom.app_surjective ι ⊤ (isAffineOpen_top Z)) n h⟩

/-- The global sections of a scheme over a field have dimension at most the sum of bounds on the
dimensions of the global sections of the members of a finite open cover. -/
theorem finrank_le_sum_of_openCover {K : Type u} [Field K] {Z : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (𝒰 : Z.OpenCover) [Fintype 𝒰.I₀] (n : 𝒰.I₀ → ℕ)
    (h : ∀ i, letI : Algebra K ↑Γ(𝒰.X i, ⊤) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ (𝒰.f i ≫ p).appTop).hom.toAlgebra
      Module.Finite K ↑Γ(𝒰.X i, ⊤) ∧ Module.finrank K ↑Γ(𝒰.X i, ⊤) ≤ n i) :
    letI : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    Module.Finite K ↑Γ(Z, ⊤) ∧ Module.finrank K ↑Γ(Z, ⊤) ≤ ∑ i, n i := by
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  let : ∀ i, Algebra K ↑Γ(𝒰.X i, ⊤) := fun i =>
    ((Scheme.ΓSpecIso (.of K)).inv ≫ (𝒰.f i ≫ p).appTop).hom.toAlgebra
  have : ∀ i, Module.Finite K ↑Γ(𝒰.X i, ⊤) := fun i => (h i).1
  let L : ↑Γ(Z, ⊤) →ₗ[K] (∀ i, ↑Γ(𝒰.X i, ⊤)) :=
    LinearMap.pi fun i => appTopLinearMap p (𝒰.f i)
  have hL : Function.Injective L := fun x y hxy => 𝒰.ext_elem x y fun i => congrFun hxy i
  refine ⟨Module.Finite.of_injective L hL, ?_⟩
  calc Module.finrank K ↑Γ(Z, ⊤) ≤ Module.finrank K (∀ i, ↑Γ(𝒰.X i, ⊤)) :=
        LinearMap.finrank_le_finrank_of_injective hL
    _ = ∑ i, Module.finrank K ↑Γ(𝒰.X i, ⊤) := by
      simpa using (Module.finrank_pi_fintype (R := K) (M := fun i : 𝒰.I₀ => ↑Γ(𝒰.X i, ⊤)))
    _ ≤ ∑ i, n i := Finset.sum_le_sum fun i _ => (h i).2

/-- A scheme with no points has global sections of dimension zero over any field in the base. -/
theorem finrank_eq_zero_of_isEmpty {K : Type u} [Field K] {Z : Scheme.{u}} [IsEmpty Z]
    (p : Z ⟶ Spec (.of K)) :
    letI : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
    Module.Finite K ↑Γ(Z, ⊤) ∧ Module.finrank K ↑Γ(Z, ⊤) = 0 := by
  let : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  have : Subsingleton ↑Γ(Z, ⊤) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mp
      ⟨fun q ↦ (isEmptyElim (Z.isoSpec.inv q : Z) : False)⟩
  exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩

/-- A field-valued base change of a finite morphism of affine schemes has global sections of
dimension at most the number of generators of the global sections of the source as a module over
the global sections of the target.

The square of global sections is a pushout of commutative rings, so the global sections of the
base change are the tensor product of those of the source with the field, and the images of the
generators span it. -/
theorem finrank_le_of_isPullback_of_isFinite {T V P : Scheme.{u}} {K : Type u} [Field K]
    (π : T ⟶ V) [IsFinite π] [IsAffine V] {c : Spec (.of K) ⟶ V}
    {fst : P ⟶ T} {snd : P ⟶ Spec (.of K)} (sq : IsPullback fst snd π c)
    {n : ℕ} (s : Fin n → ↑Γ(T, ⊤))
    (hs : letI := π.appTop.hom.toAlgebra
      Submodule.span ↑Γ(V, ⊤) (Set.range s) = ⊤) :
    letI := ((Scheme.ΓSpecIso (.of K)).inv ≫ snd.appTop).hom.toAlgebra
    Module.Finite K ↑Γ(P, ⊤) ∧ Module.finrank K ↑Γ(P, ⊤) ≤ n := by
  have : IsAffine T := isAffine_of_isAffineHom π
  have : IsAffine P := IsAffine.of_isPullback sq
  have hpush := (isPushout_appTop_of_isPullback sq).flip
  algebraize [π.appTop.hom, c.appTop.hom, fst.appTop.hom, snd.appTop.hom,
    snd.appTop.hom.comp c.appTop.hom]
  have htower : IsScalarTower ↑Γ(V, ⊤) ↑Γ(T, ⊤) ↑Γ(P, ⊤) :=
    .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hpush.1.1)
  have hpush' : Algebra.IsPushout ↑Γ(V, ⊤) ↑Γ(Spec (.of K), ⊤) ↑Γ(T, ⊤) ↑Γ(P, ⊤) :=
    CommRingCat.isPushout_iff_isPushout.mp hpush
  set e := (Algebra.IsPushout.equiv ↑Γ(V, ⊤) ↑Γ(Spec (.of K), ⊤) ↑Γ(T, ⊤)
    ↑Γ(P, ⊤)).toLinearEquiv with he
  have hspanT : Submodule.span ↑Γ(Spec (.of K), ⊤)
      (Set.range (fun i : Fin n => (1 : ↑Γ(Spec (.of K), ⊤)) ⊗ₜ[↑Γ(V, ⊤)] s i)) = ⊤ := by
    have h0 : Submodule.baseChange ↑Γ(Spec (.of K), ⊤)
        (Submodule.span ↑Γ(V, ⊤) (Set.range s)) = ⊤ := by
      rw [hs, Submodule.baseChange_top]
    rw [Submodule.baseChange_span] at h0
    have himg : (TensorProduct.mk ↑Γ(V, ⊤) ↑Γ(Spec (.of K), ⊤) ↑Γ(T, ⊤) 1) '' Set.range s =
        Set.range (fun i : Fin n => (1 : ↑Γ(Spec (.of K), ⊤)) ⊗ₜ[↑Γ(V, ⊤)] s i) := by
      rw [← Set.range_comp]
      rfl
    rwa [himg] at h0
  have hspanP : Submodule.span ↑Γ(Spec (.of K), ⊤)
      (Set.range (fun i : Fin n => e ((1 : ↑Γ(Spec (.of K), ⊤)) ⊗ₜ[↑Γ(V, ⊤)] s i))) = ⊤ := by
    have h1 := congrArg (Submodule.map e.toLinearMap) hspanT
    rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] at h1
    rw [← h1, ← Set.range_comp]
    rfl
  let algK : Algebra K ↑Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom.toAlgebra
  let algKP : Algebra K ↑Γ(P, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ snd.appTop).hom.toAlgebra
  have htowerK : IsScalarTower K ↑Γ(Spec (.of K), ⊤) ↑Γ(P, ⊤) := .of_algebraMap_eq' rfl
  have hsurjK : Function.Surjective (algebraMap K ↑Γ(Spec (.of K), ⊤)) :=
    ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (.of K)).inv).1 inferInstance).2
  have hspanK : Submodule.span K
      (Set.range (fun i : Fin n => e ((1 : ↑Γ(Spec (.of K), ⊤)) ⊗ₜ[↑Γ(V, ⊤)] s i))) = ⊤ := by
    rw [← Submodule.restrictScalars_span K ↑Γ(Spec (.of K), ⊤) hsurjK, hspanP]
    rfl
  refine ⟨Module.finite_def.mpr
    (Submodule.fg_iff_exists_fin_generating_family.mpr ⟨n, _, hspanK⟩), ?_⟩
  simpa using finrank_le_of_span_eq_top hspanK

/-- If the image of `U` under `f` lies in `V` and the point `q` misses `V`, then any scheme
completing `U.ι ≫ f` and `q` to a commutative square has no points. -/
private theorem isEmpty_of_commSq_of_not_range_subset {X Y W : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Y) {U : X.Opens} {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V) {q : Spec (.of K) ⟶ Y}
    {w₁ : W ⟶ U.toScheme} {w₂ : W ⟶ Spec (.of K)} (sq : CommSq w₁ w₂ (U.ι ≫ f) q)
    (hran : ¬ Set.range q.base ⊆ Set.range V.ι.base) : IsEmpty W := by
  refine ⟨fun x => hran ?_⟩
  rintro _ ⟨t, rfl⟩
  have hzx : q.base t = (w₂ ≫ q).base x := by
    rw [Scheme.Hom.comp_base]
    exact congrArg q.base (Subsingleton.elim _ _)
  have hmem : (U.ι (w₁ x) : X) ∈ (U : Set X) := by
    rw [← Scheme.Opens.range_ι U]
    exact Set.mem_range_self _
  rw [Scheme.Opens.range_ι, hzx, ← sq.w]
  simpa using hUV hmem

/-- For a quasi-finite morphism `f` and a pair of affine opens `U` of the source and `V` of the
target with `f '' U ⊆ V`, there is a bound, independent of the base, on the dimension of the
global sections of every field-valued base change of `U.ι ≫ f`; moreover every such base change
is affine.

The bound is the number of generators of the finite subalgebra produced for the restriction of
`f` to `U` over `V` by Zariski's main theorem, Tag 03GU. A base change along a point of `V` is
the base change of the finite half of that factorization, restricted to an open subscheme. -/
theorem exists_finrank_fibre_bound_of_affine_pair {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] {U : X.Opens} {V : Y.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    ∃ n : ℕ, ∀ (K : Type u) (_ : Field K) (q : Spec (.of K) ⟶ Y) (W : Scheme.{u})
      (w₁ : W ⟶ U.toScheme) (w₂ : W ⟶ Spec (.of K)), IsPullback w₁ w₂ (U.ι ≫ f) q →
      IsAffine W ∧
        letI : Algebra K ↑Γ(W, ⊤) :=
          ((Scheme.ΓSpecIso (.of K)).inv ≫ w₂.appTop).hom.toAlgebra
        Module.Finite K ↑Γ(W, ⊤) ∧ Module.finrank K ↑Γ(W, ⊤) ≤ n := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  obtain ⟨T, _, j, π, _, _, hfac⟩ :=
    exists_isOpenImmersion_isFinite_factorization (f.resLE V U hUV)
  let algVT : Algebra ↑Γ(V.toScheme, ⊤) ↑Γ(T, ⊤) := π.appTop.hom.toAlgebra
  have hmodfin : Module.Finite ↑Γ(V.toScheme, ⊤) ↑Γ(T, ⊤) := π.finite_appTop
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.finite_def.mp hmodfin)
  refine ⟨n, fun K _ q W w₁ w₂ sq => ?_⟩
  have hcomp : U.ι ≫ f = j ≫ π ≫ V.ι := by
    rw [← Category.assoc, hfac, Scheme.Hom.resLE_comp_ι]
  by_cases hran : Set.range q.base ⊆ Set.range V.ι.base
  · -- the base point lies in `V`, so `q` factors through `V`
    set q' := IsOpenImmersion.lift V.ι q hran
    have hq'fac : q' ≫ V.ι = q := IsOpenImmersion.lift_fac V.ι q hran
    -- base change of the finite half
    have sqD : IsPullback (pullback.fst π q') (pullback.snd π q') π q' :=
      IsPullback.of_hasPullback π q'
    have sqD' : IsPullback (pullback.fst π q') (pullback.snd π q') (π ≫ V.ι) q := by
      simpa only [hq'fac] using isPullback_comp_mono sqD V.ι
    have : IsAffine (pullback π q') := IsAffine.of_isPullback sqD
    have hDbound := finrank_le_of_isPullback_of_isFinite π sqD s hs
    -- base change of the open-immersion half
    have sqE : IsPullback (pullback.fst j (pullback.fst π q'))
        (pullback.snd j (pullback.fst π q')) j (pullback.fst π q') :=
      IsPullback.of_hasPullback _ _
    have hEopen : IsOpenImmersion (pullback.snd j (pullback.fst π q')) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sqE inferInstance
    have sqE' : IsPullback (pullback.fst j (pullback.fst π q'))
        (pullback.snd j (pullback.fst π q') ≫ pullback.snd π q') (U.ι ≫ f) q := by
      rw [hcomp]
      exact sqE.paste_vert sqD'
    obtain ⟨hEaff, hEbound⟩ := isAffine_and_finrank_le_of_isOpenImmersion
      (pullback.snd π q') (pullback.snd j (pullback.fst π q')) n hDbound
    -- transport along the canonical isomorphism of the two pullbacks
    set i := IsPullback.isoIsPullback U.toScheme (Spec (.of K)) sqE' sq with hi
    have hileg : i.inv ≫ (pullback.snd j (pullback.fst π q') ≫ pullback.snd π q') = w₂ := by
      rw [← IsPullback.isoIsPullback_hom_snd U.toScheme (Spec (.of K)) sqE' sq, ← hi,
        ← Category.assoc, i.inv_hom_id, Category.id_comp]
    have hisurj : Function.Surjective i.inv.appTop.hom :=
      ((ConcreteCategory.isIso_iff_bijective
        (Scheme.Hom.appTop i.inv)).1 (Functor.map_isIso Scheme.Γ i.inv.op)).2
    refine ⟨isAffine_of_isAffineHom i.inv, ?_⟩
    have hres := finrank_le_of_surjective_appTop
      (pullback.snd j (pullback.fst π q') ≫ pullback.snd π q') i.inv hisurj n hEbound
    rwa [hileg] at hres
  · -- the base point misses `V`, so the base change has no points
    have : IsEmpty W := isEmpty_of_commSq_of_not_range_subset f hUV sq.toCommSq hran
    obtain ⟨hfin, hz⟩ := finrank_eq_zero_of_isEmpty w₂
    exact ⟨inferInstance, hfin, hz.le.trans n.zero_le⟩

/-- The affine neighbourhood data used to cover the source: for every point of the source there
is an affine open containing it whose image lies in an affine open of the target. -/
private theorem exists_affine_pair {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧ x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hfxV (f ⁻¹ᵁ V).isOpen
  exact ⟨U, V, hU, hV, hxU, hUV⟩

/-- A choice of affine neighbourhood data at each point of the source. -/
private noncomputable def affinePair {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    {p : X.Opens × Y.Opens // IsAffineOpen p.1 ∧ IsAffineOpen p.2 ∧ x ∈ p.1 ∧ p.1 ≤ f ⁻¹ᵁ p.2} :=
  Classical.choice (show Nonempty _ from by
    obtain ⟨U, V, hU, hV, hxU, hUV⟩ := exists_affine_pair f x
    exact ⟨⟨(U, V), hU, hV, hxU, hUV⟩⟩)

/-- The open cover of the source by the chosen affine neighbourhoods. -/
private noncomputable def affinePairCover {X Y : Scheme.{u}} (f : X ⟶ Y) : X.OpenCover :=
  Scheme.Cover.mkOfCovers (J := X) (obj := fun x => (affinePair f x).1.1.toScheme)
    (map := fun x => (affinePair f x).1.1.ι)
    (fun x => ⟨x, ⟨x, (affinePair f x).2.2.2.1⟩, rfl⟩)

/-- The `i`-th member of the open cover of a pullback induced by an open cover of the left factor
lies over the right factor through the second projection of the corresponding pullback. -/
private theorem openCoverOfLeft_f_snd {X Y Z : Scheme.{u}} (𝒰 : X.OpenCover)
    (f : X ⟶ Z) (g : Y ⟶ Z) (i : 𝒰.I₀) :
    (Scheme.Pullback.openCoverOfLeft 𝒰 f g).f i ≫ pullback.snd f g =
      pullback.snd (𝒰.f i ≫ f) g := by
  show pullback.map (𝒰.f i ≫ f) g f g (𝒰.f i) (𝟙 _) (𝟙 _) (Category.comp_id _)
      (by rw [Category.comp_id, Category.id_comp]) ≫ pullback.snd f g = _
  rw [pullback.lift_snd, Category.comp_id]

/-- A locally quasi-finite morphism whose source has a finite open cover on each member of which
the global sections of every field-valued base change are affine and of dimension at most `n i`
has fibre degrees bounded by the sum of the `n i`.

The fibre over a point is covered by the base changes of the members of the cover, so its global
sections are finite dimensional of dimension at most that sum; being quasi-compact and locally
quasi-finite over the Artinian spectrum of the residue field, the fibre is a finite scheme and
its degree is exactly that dimension. -/
theorem boundsFiberDegrees_of_openCover_of_finrank_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f]
    (𝒰 : X.OpenCover) [Fintype 𝒰.I₀] (n : 𝒰.I₀ → ℕ)
    (h : ∀ (i : 𝒰.I₀) (K : Type u) (_ : Field K) (q : Spec (.of K) ⟶ Y) (W : Scheme.{u})
      (w₁ : W ⟶ 𝒰.X i) (w₂ : W ⟶ Spec (.of K)), IsPullback w₁ w₂ (𝒰.f i ≫ f) q →
      IsAffine W ∧
        letI : Algebra K ↑Γ(W, ⊤) :=
          ((Scheme.ΓSpecIso (.of K)).inv ≫ w₂.appTop).hom.toAlgebra
        Module.Finite K ↑Γ(W, ⊤) ∧ Module.finrank K ↑Γ(W, ⊤) ≤ n i) :
    BoundsFiberDegrees f (∑ i, n i : ℕ) := by
  classical
  intro y
  let : Fintype (Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).I₀ :=
    inferInstanceAs (Fintype 𝒰.I₀)
  have hleg : ∀ i : 𝒰.I₀,
      (Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).f i ≫
          f.fiberToSpecResidueField y =
        pullback.snd (𝒰.f i ≫ f) (Y.fromSpecResidueField y) :=
    openCoverOfLeft_f_snd 𝒰 f _
  have hchart : ∀ i : 𝒰.I₀,
      IsAffine ((Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).X i) ∧
      let : Algebra ↑(Y.residueField y)
          ↑Γ((Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).X i, ⊤) :=
        ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
          ((Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).f i ≫
            f.fiberToSpecResidueField y).appTop).hom.toAlgebra
      Module.Finite ↑(Y.residueField y)
          ↑Γ((Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).X i, ⊤) ∧
        Module.finrank ↑(Y.residueField y)
          ↑Γ((Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).X i, ⊤) ≤ n i := by
    intro i
    have hi := h i ↑(Y.residueField y) inferInstance (Y.fromSpecResidueField y)
      (pullback (𝒰.f i ≫ f) (Y.fromSpecResidueField y))
      (pullback.fst (𝒰.f i ≫ f) (Y.fromSpecResidueField y))
      (pullback.snd (𝒰.f i ≫ f) (Y.fromSpecResidueField y))
      (IsPullback.of_hasPullback _ _)
    rwa [← hleg i] at hi
  have hsections := finrank_le_sum_of_openCover (f.fiberToSpecResidueField y)
    (Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)) n fun i => (hchart i).2
  have : ∀ i, CompactSpace
      ((Scheme.Pullback.openCoverOfLeft 𝒰 f (Y.fromSpecResidueField y)).X i) := fun i => by
    have := (hchart i).1
    infer_instance
  have : CompactSpace (f.fiber y) :=
    Scheme.OpenCover.compactSpace (Scheme.Pullback.openCoverOfLeft 𝒰 f
      (Y.fromSpecResidueField y))
  have : LocallyQuasiFinite (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyQuasiFinite (pullback.snd f (Y.fromSpecResidueField y)))
  have : IsFinite (f.fiberToSpecResidueField y) :=
    IsFinite.of_locallyQuasiFinite (f.fiberToSpecResidueField y)
  let : Algebra ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤) :=
    ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      (f.fiberToSpecResidueField y).appTop).hom.toAlgebra
  have hfin : Module.Finite ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤) := hsections.1
  exact ⟨_, by exact_mod_cast hsections.2,
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_of_basis (f.fiberToSpecResidueField y)
      (Module.finrank ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤))
      ⟨Module.finBasisOfFinrankEq ↑(Y.residueField y) ↑Γ(f.fiber y, ⊤) rfl⟩⟩

/-- **Stacks 03JA.** A locally quasi-finite morphism of finite type whose source is quasi-compact
has universally bounded fibres. -/
@[stacks 03JA]
theorem hasUniversallyBoundedFibers_of_locallyQuasiFinite {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    HasUniversallyBoundedFibers f := by
  classical
  have hbound : ∀ i : (affinePairCover f).finiteSubcover.I₀, ∃ m : ℕ,
      ∀ (K : Type u) (_ : Field K) (q : Spec (.of K) ⟶ Y) (W : Scheme.{u})
      (w₁ : W ⟶ (affinePairCover f).finiteSubcover.X i) (w₂ : W ⟶ Spec (.of K)),
      IsPullback w₁ w₂ ((affinePairCover f).finiteSubcover.f i ≫ f) q →
      IsAffine W ∧
        let : Algebra K ↑Γ(W, ⊤) :=
          ((Scheme.ΓSpecIso (.of K)).inv ≫ w₂.appTop).hom.toAlgebra
        Module.Finite K ↑Γ(W, ⊤) ∧ Module.finrank K ↑Γ(W, ⊤) ≤ m := fun i =>
    exists_finrank_fibre_bound_of_affine_pair f
      (affinePair f ((affinePairCover f).idx i.1)).2.1
      (affinePair f ((affinePairCover f).idx i.1)).2.2.1
      (affinePair f ((affinePairCover f).idx i.1)).2.2.2.2
  exact ⟨(∑ i, (hbound i).choose : ℕ), boundsFiberDegrees_of_openCover_of_finrank_le f
    (affinePairCover f).finiteSubcover (fun i => (hbound i).choose)
    fun i => (hbound i).choose_spec⟩

end AlgebraicGeometry

end
