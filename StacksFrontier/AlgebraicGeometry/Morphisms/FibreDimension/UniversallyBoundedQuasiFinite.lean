module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FieldFibreDegreeBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange

/-!
# Universally bounded fibres of a locally quasi-finite morphism

Having universally bounded fibres is an absolute notion, not a relative one: a locally
quasi-finite morphism of schemes has universally bounded fibres as soon as its *source* is
quasi-compact. This is Stacks 03JA.

The bound is produced one chart at a time. Around a point `x` of the source, choose affine opens
`x ∈ U ⊆ f ⁻¹ᵁ V`; the induced algebra map `Γ(Y, V) ⟶ Γ(X, U)` is of finite type and quasi-finite
at the prime of `x`, so the algebraic form of Zariski's main theorem supplies a module-finite
subalgebra `S' ⊆ Γ(X, U)` and an element `t ∈ S'` outside that prime with
`S'[1/t] = Γ(X, U)[1/t]`. The basic open `W = D(t)` is then an affine open neighbourhood of `x`
whose fibre over any field-valued point of `V` is a localisation of the base change of `S'`, hence
of dimension at most the number of module generators of `S'`. Quasi-compactness of the source
reduces the whole morphism to finitely many such charts, and the sheaf axiom bounds the dimension
of the ring of global sections of a fibre by the sum of the chart bounds.

## Main results

* `AlgebraicGeometry.exists_notMem_and_finrank_tensorProduct_le`: the algebraic chart bound, read
  off Zariski's main theorem.
* `AlgebraicGeometry.boundsFiberDegrees_specMap_of_finrank_le`: a uniform bound on the dimensions
  of the field base changes of an algebra bounds the degrees of the fibres of the induced morphism
  of affine schemes.
* `AlgebraicGeometry.boundsFiberDegrees_comp_isOpenImmersion`: a bound on the degrees of the
  fibres survives composition with an open immersion, the new fibres being empty outside the
  image.
* `AlgebraicGeometry.exists_isAffineOpen_mem_and_boundsFiberDegrees`: every point of the source of
  a locally quasi-finite morphism has an affine open neighbourhood over which the degrees of the
  fibres are bounded.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite` and
  `AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace`:
  Stacks 03JA, under two names.
* `AlgebraicGeometry.hasUniversallyBoundedFibers_of_isAffine` and
  `AlgebraicGeometry.hasUniversallyBoundedFibers_of_isFinite_of_isAffine`: the affine cases, for
  which quasi-compactness of the source is automatic.
* `AlgebraicGeometry.compactSpace_fiber_of_finite`: a fibre with finitely many points is
  quasi-compact.

## Implementation notes

Stacks 03JA is stated for a quasi-finite morphism, which in Mathlib's vocabulary is
`AlgebraicGeometry.LocallyQuasiFinite` together with `AlgebraicGeometry.LocallyOfFiniteType`; the
finite-type conjunct is not redundant, since `LocallyQuasiFinite` alone omits the finite-type
condition of Stacks 00PL. Quasi-compactness of the source is `CompactSpace`.

The source reduces a quasi-finite morphism of affines to a finite one by Stacks 03GU and then
bounds the degrees of a finite morphism by a number of module generators. Here the reduction is
made on the algebra side instead, so that the bound becomes a statement about the dimension of a
base change of a module-finite subalgebra; passing from that subalgebra to its localisation costs
nothing, because a localisation of an Artinian ring is a quotient of it.

The degree of a fibre is read off the ring of global sections: a morphism to the spectrum of a
field is finite locally free of rank `r` exactly when that ring has dimension `r`, which is
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_finrank_sections_eq`. The fibre of a morphism
of affine schemes is identified with the spectrum of a base change by
`AlgebraicGeometry.Spec.fiberToSpecResidueFieldIso`.

## References

* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03J6](https://stacks.math.columbia.edu/tag/03J6)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 00Q9](https://stacks.math.columbia.edu/tag/00Q9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### An auxiliary fact -/

/-- A compact scheme stays compact after passing to the source of a quasi-compact morphism. -/
private theorem compactSpace_of_quasiCompact {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [CompactSpace Y] : CompactSpace X :=
  ⟨by simpa using QuasiCompact.isCompact_preimage (f := f) Set.univ isOpen_univ isCompact_univ⟩

/-! ### The algebraic chart bound -/

/-- A base change of a module spanned by `n` elements is spanned by `n` elements, hence finite of
dimension at most `n` over a field. -/
private theorem finite_and_finrank_tensorProduct_le {R A K : Type u} [CommRing R] [CommRing A]
    [Field K] [Algebra R A] [Algebra R K] {n : ℕ} (v : Fin n → A)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    Module.Finite K (K ⊗[R] A) ∧ Module.finrank K (K ⊗[R] A) ≤ n := by
  have htop : (⊤ : Submodule R A).baseChange K = ⊤ := Submodule.baseChange_top K
  rw [← hv, Submodule.baseChange_span] at htop
  rw [← Set.range_comp] at htop
  refine ⟨⟨?_⟩, ?_⟩
  · rw [← htop]
    exact Submodule.fg_span (Set.finite_range _)
  · simpa using finrank_le_of_span_eq_top htop

/-- The algebraic chart bound behind Stacks 03JA. Let `S` be an algebra of finite type over `R`
which is quasi-finite at a prime `p` of `S`. Then there is an element `t` of `S` outside `p` and
an integer `n` such that every field base change of the localisation of `S` away from `t` has
dimension at most `n`.

Zariski's main theorem gives a module-finite subalgebra `S' ⊆ S` and an element `t ∈ S'` outside
`p` whose localisations agree, `S'[1/t] = S[1/t]`. If `S'` is spanned by `n` elements as an
`R`-module then `K ⊗[R] S'` has dimension at most `n` over `K`, and `K ⊗[R] S[1/t]` is a
localisation of it, hence a quotient, because a finite-dimensional algebra over a field is
Artinian. -/
theorem exists_notMem_and_finrank_tensorProduct_le {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (p : Ideal S) [p.IsPrime]
    [Algebra.WeaklyQuasiFiniteAt R p] :
    ∃ t : S, t ∉ p ∧ ∃ n : ℕ,
      ∀ (L : Type u) [CommRing L] [Algebra S L] [IsLocalization.Away t L]
        [Algebra R L] [IsScalarTower R S L] (K : Type u) [Field K] [Algebra R K],
        Module.Finite K (K ⊗[R] L) ∧ Module.finrank K (K ⊗[R] L) ≤ n := by
  obtain ⟨S', hfg, r, hrp, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective (R := R) (S := S) p
  obtain ⟨n, v, hv⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp
      ((Submodule.fg_top (Subalgebra.toSubmodule S')).mpr hfg)
  refine ⟨(r : S), hrp, n, ?_⟩
  intro L _ _ _ _ _ K _ _
  -- `L` is isomorphic as an `R`-algebra to the localisation of `S'` away from `r`.
  let e : L ≃ₐ[R] Localization.Away (r : S') :=
    ((IsLocalization.algEquiv (Submonoid.powers (r : S)) L
      (Localization.Away (r : S))).restrictScalars R).trans
      (AlgEquiv.ofBijective (Localization.awayMapₐ (R := R) S'.val r) hbij).symm
  obtain ⟨hDfin, hDrank⟩ := finite_and_finrank_tensorProduct_le (R := R) (A := ↥S') (K := K) v hv
  have hart : IsArtinianRing (K ⊗[R] ↥S') := IsArtinianRing.of_finite K _
  have hsurj : Function.Surjective
      (algebraMap (K ⊗[R] ↥S') (Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S')))) :=
    IsArtinianRing.localization_surjective (Submonoid.powers ((1 : K) ⊗ₜ[R] (r : ↥S'))) _
  let φ : (K ⊗[R] ↥S') →ₗ[K] Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S')) :=
    (IsScalarTower.toAlgHom K (K ⊗[R] ↥S')
      (Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S')))).toLinearMap
  have hLfin : Module.Finite K (Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S'))) :=
    Module.Finite.of_surjective φ hsurj
  have hLrank : Module.finrank K (Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S'))) ≤ n :=
    le_trans (LinearMap.finrank_le_finrank_of_surjective (f := φ) hsurj) hDrank
  let e₁ : K ⊗[R] Localization.Away (r : ↥S') ≃ₐ[K]
      Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S')) :=
    IsLocalization.Away.tensorProductEquivTMulRight R K (r : ↥S') (Localization.Away (r : ↥S'))
  let E : K ⊗[R] L ≃ₗ[K] Localization.Away ((1 : K) ⊗ₜ[R] (r : ↥S')) :=
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl K K) e.toLinearEquiv).trans
      e₁.toLinearEquiv
  exact ⟨Module.Finite.equiv E.symm, (LinearEquiv.finrank_eq E).trans_le hLrank⟩

/-! ### From the algebraic bound to a bound on fibre degrees -/

/-- The global sections of the spectrum of an algebra, with the algebra structure coming from the
induced morphism of schemes, are the algebra itself. -/
private noncomputable def gammaSpecAlgEquiv (K C : Type u) [CommRing K] [CommRing C]
    [Algebra K C] :
    letI : Algebra K ↑Γ(Spec (CommRingCat.of C), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (Spec.map (CommRingCat.ofHom (algebraMap K C))).appTop).hom.toAlgebra
    C ≃ₐ[K] ↑Γ(Spec (CommRingCat.of C), ⊤) := by
  let g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K C))
  let _ : Algebra K ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom.toAlgebra
  refine AlgEquiv.ofRingEquiv
    (f := (Scheme.ΓSpecIso (CommRingCat.of C)).symm.commRingCatIsoToRingEquiv) fun a ↦ ?_
  change (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (algebraMap K C a) =
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom a
  have hvalue : (Scheme.ΓSpecIso (CommRingCat.of C)).hom.hom
      (g.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a)) = algebraMap K C a := by
    calc _ = ((Spec.map (CommRingCat.ofHom (algebraMap K C))).appTop ≫
          (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) := rfl
      _ = ((Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫
          CommRingCat.ofHom (algebraMap K C)).hom
            ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) :=
        congrArg (fun φ : CommRingCat.of ↑Γ(Spec (CommRingCat.of K), ⊤) ⟶ CommRingCat.of C ↦
          φ.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a))
            (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap K C)))
      _ = _ := by simp
  simpa using (congrArg (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom hvalue).symm

/-- A morphism of affine schemes induced by a finite-dimensional algebra over a field is finite
locally free, of rank the dimension of that algebra. -/
theorem isFiniteLocallyFreeOfRank_specMap_algebraMap {K C : Type u} [Field K] [CommRing C]
    [Algebra K C] (d : ℕ) (hfin : Module.Finite K C) (hd : Module.finrank K C = d) :
    IsFiniteLocallyFreeOfRank (Spec.map (CommRingCat.ofHom (algebraMap K C))) d := by
  let g : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K C))
  let _ : Algebra K ↑Γ(Spec (CommRingCat.of C), ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom.toAlgebra
  let E := gammaSpecAlgEquiv K C
  have : Module.Finite K C := hfin
  rw [isFiniteLocallyFreeOfRank_iff_finrank_sections_eq g d]
  refine ⟨inferInstance, Module.Finite.equiv E.toLinearEquiv, ?_⟩
  rwa [← LinearEquiv.finrank_eq E.toLinearEquiv]

/-- A uniform bound on the dimensions of all field base changes of an algebra bounds the degrees
of the fibres of the induced morphism of affine schemes. -/
theorem boundsFiberDegrees_specMap_of_finrank_le {A L : Type u} [CommRing A] [CommRing L]
    [Algebra A L] (n : ℕ)
    (h : ∀ (K : Type u) [Field K] [Algebra A K],
      Module.Finite K (K ⊗[A] L) ∧ Module.finrank K (K ⊗[A] L) ≤ n) :
    BoundsFiberDegrees (Spec.map (CommRingCat.ofHom (algebraMap A L))) (n : ℤ) := by
  intro q
  have : (q : PrimeSpectrum A).asIdeal.IsPrime := (q : PrimeSpectrum A).isPrime
  obtain ⟨hfin, hrank⟩ := h q.asIdeal.ResidueField
  refine ⟨Module.finrank q.asIdeal.ResidueField (q.asIdeal.Fiber L), by exact_mod_cast hrank, ?_⟩
  exact ((IsFiniteLocallyFreeOfRank.property
    (Module.finrank q.asIdeal.ResidueField (q.asIdeal.Fiber L))).arrow_mk_iso_iff
      (Spec.fiberToSpecResidueFieldIso A L q)).mpr
    (isFiniteLocallyFreeOfRank_specMap_algebraMap _ hfin rfl)

/-- A bound on the degrees of the fibres of a morphism survives composition with an open
immersion: the new fibres over points outside the image are empty, and over points of the image
they agree with the old ones. -/
theorem boundsFiberDegrees_comp_isOpenImmersion {W V Y : Scheme.{u}} (h : W ⟶ V) (j : V ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) (hb : BoundsFiberDegrees h (n : ℤ)) :
    BoundsFiberDegrees (h ≫ j) (n : ℤ) := by
  rw [boundsFiberDegrees_iff_field_baseChange] at hb ⊢
  intro K _ g
  by_cases hr : Set.range g.base ⊆ Set.range j.base
  · obtain ⟨r, hrn, hrank⟩ := hb K (IsOpenImmersion.lift j g hr)
    refine ⟨r, hrn, ?_⟩
    have sq : IsPullback (pullback.fst (IsOpenImmersion.lift j g hr) h)
        (pullback.snd (IsOpenImmersion.lift j g hr) h) g (h ≫ j) := by
      have := isPullback_comp_mono
        (IsPullback.of_hasPullback (IsOpenImmersion.lift j g hr) h) j
      rwa [IsOpenImmersion.lift_fac j g hr] at this
    have hpb := IsPullback.of_hasPullback g (h ≫ j)
    refine ((IsFiniteLocallyFreeOfRank.property r).cancel_left_of_respectsIso
      (sq.isoIsPullback _ _ hpb).hom (pullback.fst g (h ≫ j))).mp ?_
    rwa [sq.isoIsPullback_hom_fst _ _ hpb]
  · refine ⟨0, by positivity, ?_⟩
    have hempty : IsEmpty ↥(pullback g (h ≫ j)) := by
      refine ⟨fun z ↦ hr ?_⟩
      have hz : g.base (pullback.fst g (h ≫ j) z) =
          j.base (h.base (pullback.snd g (h ≫ j) z)) := by
        simpa using congrArg (fun φ : pullback g (h ≫ j) ⟶ Y ↦ φ.base z)
          (pullback.condition (f := g) (g := h ≫ j))
      rintro _ ⟨a, rfl⟩
      rw [Subsingleton.elim a (pullback.fst g (h ≫ j) z), hz]
      exact ⟨_, rfl⟩
    exact isFiniteLocallyFreeOfRank_zero_of_isEmpty _

/-! ### The chart bound on a scheme -/

/-- Every point of the source of a locally quasi-finite morphism of finite type has an affine open
neighbourhood over which the degrees of the fibres are bounded. -/
theorem exists_isAffineOpen_mem_and_boundsFiberDegrees {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (x : X) :
    ∃ (W : X.Opens) (n : ℕ), x ∈ W ∧ IsAffineOpen W ∧ BoundsFiberDegrees (W.ι ≫ f) (n : ℤ) := by
  obtain ⟨V, hV, hfxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ (f x))
  obtain ⟨U, hU, hxU, hUV'⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hfxV)
  have hUV : U ≤ f ⁻¹ᵁ V := hUV'
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have hft : Algebra.FiniteType ↑Γ(Y, V) ↑Γ(X, U) := f.finiteType_appLE hV hU hUV
  have hqf : Algebra.QuasiFiniteAt ↑Γ(Y, V) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    (f.quasiFiniteAt x).quasiFiniteAt hU hV hUV hxU
  obtain ⟨t, htp, n, hbound⟩ :=
    exists_notMem_and_finrank_tensorProduct_le (R := ↑Γ(Y, V)) (S := ↑Γ(X, U))
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  have hWU : X.basicOpen t ≤ U := X.basicOpen_le t
  have hWV : X.basicOpen t ≤ f ⁻¹ᵁ V := hWU.trans hUV
  refine ⟨X.basicOpen t, n, ?_, hU.basicOpen t, ?_⟩
  · rw [← hU.fromSpec_image_basicOpen]
    exact ⟨hU.primeIdealOf ⟨x, hxU⟩, htp, hU.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
  -- The chart is the basic open `D(t)`, whose sections localise `Γ(X, U)` away from `t`.
  let _ : Algebra ↑Γ(Y, V) ↑Γ(X, X.basicOpen t) := (f.appLE V (X.basicOpen t) hWV).hom.toAlgebra
  have htower : IsScalarTower ↑Γ(Y, V) ↑Γ(X, U) ↑Γ(X, X.basicOpen t) := by
    refine .of_algebraMap_eq fun a ↦ ?_
    show (f.appLE V (X.basicOpen t) hWV).hom a = _
    rw [← Scheme.Hom.appLE_map f hUV (homOfLE hWU).op]
    rfl
  have hloc : IsLocalization.Away t ↑Γ(X, X.basicOpen t) := hU.isLocalization_basicOpen t
  have hspec : BoundsFiberDegrees
      (Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y, V) ↑Γ(X, X.basicOpen t)))) (n : ℤ) :=
    boundsFiberDegrees_specMap_of_finrank_le n (hbound ↑Γ(X, X.basicOpen t))
  -- Transport the bound to the restriction `D(t) ⟶ V` and then to `D(t) ⟶ Y`.
  have _ : IsAffine (X.basicOpen t).toScheme := hU.basicOpen t
  have _ : IsAffine V.toScheme := hV
  have hres : BoundsFiberDegrees (f.resLE V (X.basicOpen t) hWV) (n : ℤ) := by
    have hmap : Spec.map (CommRingCat.ofHom (algebraMap ↑Γ(Y, V) ↑Γ(X, X.basicOpen t))) =
        Spec.map (f.appLE V (X.basicOpen t) hWV) := rfl
    rw [hmap] at hspec
    let P : MorphismProperty Scheme.{u} := fun _ _ g ↦ BoundsFiberDegrees g (n : ℤ)
    have _ : P.RespectsIso := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
    show P (f.resLE V (X.basicOpen t) hWV)
    rw [P.arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine (f.resLE V (X.basicOpen t) hWV)),
      Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, Spec.map_comp, Spec.map_comp,
      Category.assoc, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
    exact hspec
  have hfinal := boundsFiberDegrees_comp_isOpenImmersion (f.resLE V (X.basicOpen t) hWV) V.ι n hres
  rwa [Scheme.Hom.resLE_comp_ι] at hfinal

/-! ### Stacks 03JA -/

/-- The dimension of the ring of global sections of a scheme is at most the sum of the dimensions
over a finite open cover: a global section is determined by its restrictions. -/
private theorem finite_and_finrank_le_sum_of_openCover {K : Type u} [Field K] {Z : Scheme.{u}}
    (𝒰 : Z.OpenCover) [Fintype 𝒰.I₀] [Module K ↑Γ(Z, ⊤)] [∀ i, Module K ↑Γ(𝒰.X i, ⊤)]
    (n : 𝒰.I₀ → ℕ) (hfinite : ∀ i, Module.Finite K ↑Γ(𝒰.X i, ⊤))
    (hbound : ∀ i, Module.finrank K ↑Γ(𝒰.X i, ⊤) ≤ n i)
    (hcompat : ∀ i (a : K) (s : ↑Γ(Z, ⊤)),
      (𝒰.f i).appTop (a • s) = a • (𝒰.f i).appTop s) :
    Module.Finite K ↑Γ(Z, ⊤) ∧ Module.finrank K ↑Γ(Z, ⊤) ≤ ∑ i, n i := by
  let L : ↑Γ(Z, ⊤) →ₗ[K] ∀ i, ↑Γ(𝒰.X i, ⊤) :=
    { toFun := fun s i ↦ (𝒰.f i).appTop s
      map_add' s s' := funext fun i ↦ by simp
      map_smul' a s := funext fun i ↦ hcompat i a s }
  have hL : Function.Injective L := fun s s' hss' ↦ 𝒰.ext_elem s s' fun i ↦ congrFun hss' i
  have _ : ∀ i, Module.Finite K ↑Γ(𝒰.X i, ⊤) := hfinite
  refine ⟨Module.Finite.of_injective L hL, ?_⟩
  calc Module.finrank K ↑Γ(Z, ⊤)
      ≤ Module.finrank K (∀ i, ↑Γ(𝒰.X i, ⊤)) := LinearMap.finrank_le_finrank_of_injective hL
    _ = ∑ i, Module.finrank K ↑Γ(𝒰.X i, ⊤) := by
      simpa using Module.finrank_pi_fintype (R := K) (M := fun i : 𝒰.I₀ ↦ ↑Γ(𝒰.X i, ⊤))
    _ ≤ ∑ i, n i := Finset.sum_le_sum fun i _ ↦ hbound i

/-- **Stacks 03JA**, with the quasi-compactness of the source named in the statement. This is
`AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite`; the two differ only in
their names. -/
theorem hasUniversallyBoundedFibers_of_locallyQuasiFinite_of_compactSpace {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    HasUniversallyBoundedFibers f :=
  hasUniversallyBoundedFibers_of_locallyQuasiFinite f

/-- **Stacks 03JA for a quasi-finite morphism of affine schemes.** An affine scheme is
quasi-compact, so no hypothesis beyond affineness of the source is needed. -/
theorem hasUniversallyBoundedFibers_of_isAffine {U V : Scheme.{u}} (g : U ⟶ V)
    [IsAffine U] [IsAffine V] [LocallyOfFiniteType g] [LocallyQuasiFinite g] :
    HasUniversallyBoundedFibers g :=
  hasUniversallyBoundedFibers_of_locallyQuasiFinite g

/-- **Stacks 03JA for a finite morphism of affine schemes.** A finite morphism is locally of
finite type and locally quasi-finite, so this is the previous statement. -/
theorem hasUniversallyBoundedFibers_of_isFinite_of_isAffine {Z V : Scheme.{u}} (π : Z ⟶ V)
    [IsAffine Z] [IsAffine V] [IsFinite π] : HasUniversallyBoundedFibers π :=
  hasUniversallyBoundedFibers_of_isAffine π

/-- A fibre of a morphism of schemes with finitely many points is quasi-compact. -/
theorem compactSpace_fiber_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (h : (f ⁻¹' {y}).Finite) : CompactSpace (f.fiber y) := by
  have := h.to_subtype
  have h2 : Finite (f.fiber y) := Finite.of_equiv _ (f.fiberHomeo y).toEquiv.symm
  infer_instance

end AlgebraicGeometry

end
