module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicard.NormalizedDivisors
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.IdealSheafComap
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.PicardScheme.CurvePicardScheme
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSectionsEqualizer

/-!
# Families of divisors with a normalized invertible sheaf

Let `X` be a geometrically irreducible smooth proper curve over a field `k`, covered by two
affine opens, and `T` a scheme over `k`. Two degree-`d` families of divisors `D₁, D₂` on `X_T`
(points of the Hilbert functor `Hilb^d_{X/k}(T)`) whose invertible sheaves differ by an invertible
module on `T`, and such that every fibre of `𝒪(D₁)` has `H¹ = 0` and `dim H⁰ = 1`, are equal.
This is the injectivity half of the proof of [Stacks, Tag 0B9X], reduced to affine charts of `T`
on which the twisting module is trivial.

## Main results

* `Stacks.PicardCurve.exists_chart`: an affine chart `Spec R ⟶ T` inside a given open.
* `Stacks.PicardCurve.eq_of_picardClass_eq_add`: the injectivity statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Divisors (IsEffectiveCartierDivisor IsRelativeEffectiveCartierDivisor divisorSheaf
  invertibleSheaf')
open Stacks.FibreCohomology (fibreCohomology)

universe u

namespace Stacks.PicardCurve

/-- **Ideal sheaves agreeing on an open cover are equal.** -/
theorem eq_of_comap_eq_of_isOpenImmersion {Y : Scheme.{u}} {ι : Type*} {Z : ι → Scheme.{u}}
    (g : ∀ i, Z i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
    (hg : ⋃ i, Set.range (g i).base = Set.univ) {I J : Y.IdealSheafData}
    (h : ∀ i, I.comap (g i) = J.comap (g i)) : I = J := by
  have : ∀ p : Σ i, (Z i).affineOpens, IsAffine (p.2 : (Z p.1).Opens) := fun p => p.2.2
  refine Scheme.IdealSheafData.eq_of_comap_eq_of_iUnion_range_eq_univ
    (Z := fun p : Σ i, (Z i).affineOpens => ((p.2 : (Z p.1).Opens) : Scheme.{u}))
    (fun p => (p.2 : (Z p.1).Opens).ι ≫ g p.1) ?_ fun p => ?_
  · refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hg ▸ Set.mem_univ y : y ∈ ⋃ i, Set.range (g i).base)
    obtain ⟨z, rfl⟩ := hi
    obtain ⟨W, hW, hzW, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z i) (x := z)
      (U := ⊤) trivial
    refine Set.mem_iUnion.2 ⟨⟨i, ⟨W, hW⟩⟩, ⟨⟨z, hzW⟩, ?_⟩⟩
    rfl
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp, h p.1]

variable {k : Type u} [Field k]

/-- **An affine chart of a `k`-scheme inside a given open**: an open immersion `Spec R ⟶ T` from
the spectrum of a `k`-algebra, through a given point, landing in a given open, over `k`. -/
theorem exists_chart {T : Scheme.{u}} (a : T ⟶ Spec (.of k)) (O : T.Opens) (t : T)
    (ht : t ∈ O) :
    ∃ (R : Type u) (_ : CommRing R) (_ : Algebra k R) (ι : Spec (.of R) ⟶ T),
      IsOpenImmersion ι ∧ Set.range ι ⊆ (O : Set T) ∧ t ∈ Set.range ι ∧
        Spec.map (CommRingCat.ofHom (algebraMap k R)) = ι ≫ a := by
  obtain ⟨V, hV, htV, hVO⟩ := exists_isAffineOpen_mem_and_subset (X := T) (x := t) (U := O) ht
  let R : Type u := Γ(T, V)
  let ι : Spec (.of R) ⟶ T := hV.fromSpec
  let φ : CommRingCat.of k ⟶ CommRingCat.of R := Spec.preimage (ι ≫ a)
  let : Algebra k R := φ.hom.toAlgebra
  refine ⟨R, inferInstance, this, ι, inferInstance, ?_, ?_, ?_⟩
  · change Set.range hV.fromSpec ⊆ _
    rw [hV.range_fromSpec]; exact hVO
  · change t ∈ Set.range hV.fromSpec
    rw [hV.range_fromSpec]; exact htV
  · change Spec.map (CommRingCat.ofHom φ.hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- A point of the corner of a cartesian square of schemes over two compatible points. -/
theorem exists_preimage_of_isPullback {P X' Y Z : Scheme.{u}} {fst : P ⟶ X'} {snd : P ⟶ Y}
    {f : X' ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (x : X') (y : Y) (hxy : f x = g y) :
    ∃ p : P, fst p = x ∧ snd p = y := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz₂]

/-- **The kernel of the residue map at a point is the image point.** For `g : Y ⟶ Spec R` and a
point `y`, the kernel of the ring map `R → κ(y)` corresponding to `Spec κ(y) ⟶ Y ⟶ Spec R` is
the prime `g(y)`. -/
theorem ker_preimage_fromSpecResidueField_comp {R : Type u} [CommRing R] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of R)) (y : Y) :
    RingHom.ker (Spec.preimage (Y.fromSpecResidueField y ≫ g)).hom = (g y).asIdeal := by
  set φ := Spec.preimage (Y.fromSpecResidueField y ≫ g)
  have hφ : Spec.map φ = Y.fromSpecResidueField y ≫ g := Spec.map_preimage _
  let c : Spec (Y.residueField y) := IsLocalRing.closedPoint (Y.residueField y)
  have h1 : Spec.map φ c = g y := by
    rw [hφ, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have h2 : (Spec.map φ c).asIdeal = Ideal.comap φ.hom c.asIdeal := rfl
  have hc : c.asIdeal = ⊥ := by
    change IsLocalRing.maximalIdeal _ = ⊥
    exact IsLocalRing.maximalIdeal_eq_bot
  have h3 : (g y).asIdeal = (Spec.map φ c).asIdeal := congrArg PrimeSpectrum.asIdeal h1.symm
  rw [h3, h2, hc, RingHom.ker_eq_comap_bot]

/-- A section whose pullback along a composite is nonzero has a nonzero pullback along the
first map of the pullback along the second. -/
theorem pullbackGlobalSections_ne_zero_of_comp {Y₁ Y₂ Y₃ : Scheme.{u}} (f₁ : Y₁ ⟶ Y₂)
    (f₂ : Y₂ ⟶ Y₃) (F : Y₃.Modules) (s : Γ(F, ⊤))
    (h : pullbackGlobalSections (f₁ ≫ f₂) F s ≠ 0) :
    pullbackGlobalSections f₁ ((Scheme.Modules.pullback f₂).obj F)
      (pullbackGlobalSections f₂ F s) ≠ 0 := by
  intro h0
  apply h
  rw [← AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_comp, h0, map_zero]

/-- The base change of a proper morphism to the base of a `k`-scheme `T` is proper. -/
private theorem isProper_baseChange_hom {X T : Scheme.{u}} (fX : X ⟶ Spec (.of k)) [IsProper fX]
    (a : T ⟶ Spec (.of k)) : IsProper ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback fX a) inferInstance

/-- The base change of `fX` along a chart `ι : Spec R ⟶ T` over `k` is cartesian over
`Spec R ⟶ Spec k`. -/
private theorem isPullback_fst_baseChange_of_algebraMap {X T : Scheme.{u}}
    (fX : X ⟶ Spec (.of k)) (a : T ⟶ Spec (.of k)) {R : Type u} [CommRing R] [Algebra k R]
    (ι : Spec (.of R) ⟶ T) (h : Spec.map (CommRingCat.ofHom (algebraMap k R)) = ι ≫ a) :
    IsPullback (pullback.fst fX (ι ≫ a))
      ((Over.pullback (Over.mk (ι ≫ a)).hom).obj (Over.mk fX)).hom fX
      (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
  (congrArg (fun φ => IsPullback (pullback.fst fX (ι ≫ a)) _ fX φ) h).mpr
    (IsPullback.of_hasPullback fX (ι ≫ a))

section Families

attribute [local instance] AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve

variable {X : Scheme.{u}} (fX : X ⟶ Spec (.of k))
  [IsCurve k fX] [GeometricallyIrreducible fX] [Smooth fX] [IsProper fX]
  (U : Stacks.TwoAffineCech.Cover.{u} → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

omit [GeometricallyIrreducible fX] in
include hU hUaff in
/-- **Two degree-`d` families of divisors on `X_T` whose invertible sheaves differ by an
invertible module on `T`, and whose sheaf has normalized fibres (`H¹ = 0`, `dim H⁰ = 1`), are
equal.** -/
theorem eq_of_picardClass_eq_add {T : Scheme.{u}} (a : T ⟶ Spec (.of k)) {d : ℕ}
    (D₁ D₂ : Stacks.Hilbert.HilbertFamily (Over.mk fX) (Over.mk a) d)
    (N : Stacks.Picard.ofScheme T)
    (hcls : D₂.picardClass = D₁.picardClass +
      Stacks.Picard.schemePullbackClass ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom N)
    (h1 : ∀ t : T, Module.finrank (T.residueField t) (fibreCohomology
      ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom (divisorSheaf D₁.ideal) t 1) = 0)
    (h0 : ∀ t : T, Module.finrank (T.residueField t) (fibreCohomology
      ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom (divisorSheaf D₁.ideal) t 0) = 1) :
    D₁ = D₂ := by
  have hsm : SmoothOfRelativeDimension 1 (Over.mk fX).hom :=
    AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve k fX
  set fT := ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom with hfT
  have : IsProper fT := isProper_baseChange_hom fX a
  have hD₁ := D₁.isEffectiveCartierDivisor_ideal
  have hD₂ := D₂.isEffectiveCartierDivisor_ideal
  have : (divisorSheaf D₁.ideal).IsQuasicoherent := Stacks.AbelMap.isQuasicoherent_divisorSheaf _
  refine Stacks.Hilbert.HilbertFamily.ext ?_
  choose O hO hNO using fun t : T => Stacks.Picard.exists_mem_schemePullbackClass_eq_zero N t
  choose R instR instA ι hι hιO htι hRalg using fun t => exists_chart a (O t) t (hO t)
  let g : ∀ t, (Over.mk (ι t ≫ a) : Over (Spec (.of k))) ⟶ Over.mk a := fun t =>
    Over.homMk (ι t) rfl
  let q : ∀ t, _ := fun t => Stacks.Hilbert.familyBaseChangeMap (Over.mk fX) (g t)
  have hq : ∀ t, IsPullback (q t) ((Over.pullback (Over.mk (ι t ≫ a)).hom).obj (Over.mk fX)).hom
      fT (ι t) := fun t => Stacks.Hilbert.isPullback_familyBaseChangeMap (Over.mk fX) (g t)
  have : ∀ t, IsOpenImmersion (q t) := fun t =>
    have := hι t
    MorphismProperty.of_isPullback (hq t).flip inferInstance
  have hcov : ⋃ t, Set.range (q t).base = Set.univ := by
    refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨fT x, ?_⟩
    obtain ⟨z, hz⟩ := htι (fT x)
    obtain ⟨p, hp, -⟩ := exists_preimage_of_isPullback (hq (fT x)) x z hz.symm
    exact ⟨p, hp⟩
  refine eq_of_comap_eq_of_isOpenImmersion q hcov fun t => ?_
  let := instR t
  let := instA t
  let E₁ := Stacks.Hilbert.baseChange (Over.mk fX) (g t) D₁
  let E₂ := Stacks.Hilbert.baseChange (Over.mk fX) (g t) D₂
  change E₁.ideal = E₂.ideal
  set fR := ((Over.pullback (Over.mk (ι t ≫ a)).hom).obj (Over.mk fX)).hom
  have hRsq := isPullback_fst_baseChange_of_algebraMap fX a (ι t) (hRalg t)
  have : SmoothOfRelativeDimension 1 fR :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback fX (ι t ≫ a)) hsm
  have hE : ∀ E : Stacks.Hilbert.HilbertFamily (Over.mk fX) (Over.mk (ι t ≫ a)) d,
      IsRelativeEffectiveCartierDivisor fR E.ideal := fun E =>
    have := E.isFiniteLocallyFreeOfRank
    have : Stacks.Morphisms.IsFiniteLocallyFree (E.ideal.subschemeι ≫ fR) :=
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ d
    isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree fR E.ideal
  have hE₁ := hE E₁
  have hE₂ := hE E₂
  have : IsEffectiveCartierDivisor E₁.ideal := hE₁.1
  have : IsEffectiveCartierDivisor E₂.ideal := hE₂.1
  -- the two sheaves agree on the chart
  have hpb : ∀ D : Stacks.Hilbert.HilbertFamily (Over.mk fX) (Over.mk a) d,
      (Stacks.Hilbert.baseChange (Over.mk fX) (g t) D).picardClass =
        Stacks.Picard.schemePullbackClass (q t) D.picardClass := fun D =>
    (Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass D
      (Stacks.Hilbert.baseChange (Over.mk fX) (g t) D) (q t) rfl).symm
  have hlift : Set.range (ι t).base ⊆ Set.range (O t).ι.base := by
    rw [Scheme.Opens.range_ι]; exact hιO t
  have hfac := IsOpenImmersion.lift_fac (O t).ι (ι t) hlift
  have hNι : Stacks.Picard.schemePullbackClass (ι t) N = 0 := by
    rw [← hfac, ← Stacks.Picard.schemePullbackClass_comp, hNO t]
    exact map_zero (Stacks.Picard.schemePullbackClassHom _)
  have hcls' : E₂.picardClass = E₁.picardClass := by
    rw [hpb D₂, hpb D₁, hcls, Stacks.Picard.schemePullbackClass_add,
      Stacks.Picard.schemePullbackClass_comp, (hq t).w, ← Stacks.Picard.schemePullbackClass_comp,
      hNι]
    rw [show Stacks.Picard.schemePullbackClass fR
        (0 : Stacks.Picard.ofScheme (Spec (.of (R t)))) = 0
      from map_zero (Stacks.Picard.schemePullbackClassHom _), add_zero]
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).1 hcls'
  -- the fibres on the chart are those of `D₁`
  have : Stacks.Divisors.IsPullbackDefined (q t) D₁.ideal := hE₁.1
  have hfib : ∀ (x : Spec (.of (R t))) (n : ℕ),
      Module.finrank ((Spec (.of (R t))).residueField x)
          (fibreCohomology fR (divisorSheaf E₁.ideal) x n) =
        Module.finrank (T.residueField (ι t x))
          (fibreCohomology fT (divisorSheaf D₁.ideal) (ι t x) n) :=
    fun x n => Stacks.FibreCohomology.finrank_fibreCohomology_eq_of_isPullback fT
      (divisorSheaf D₁.ideal) (q t) fR (ι t) (hq t) (divisorSheaf E₁.ideal)
      (Stacks.Divisors.invertibleSheafPullbackIso (q t) D₁.ideal).symm x n
  exact eq_of_divisorSheaf_iso fX U hU hUaff (pullback.fst fX (ι t ≫ a)) fR hRsq E₁.ideal E₂.ideal
    hE₁ hE₂ e (fun x => (hfib x 1).trans (h1 _)) (fun x => (hfib x 0).trans (h0 _))

include hU hUaff in
/-- **Locally on the base, a point of the Picard group with normalized fibres is the class of a
family of divisors of degree `g`** ([Stacks, Tag 0B9X], the claim): around every point of `T`
there is an open `O` and a degree-`g` family `D` on `X_O` with `[𝒪(D)] = x|_O`. -/
theorem exists_hilbertFamily_picardClass_eq {T : Scheme.{u}} (a : T ⟶ Spec (.of k))
    (x : Stacks.Picard.ofScheme ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).left)
    (h1 : ∀ t : T, classFibreRank ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom x t 1 = 0)
    (h0 : ∀ t : T, classFibreRank ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom x t 0 = 1)
    (t₀ : T) :
    ∃ (O : T.Opens) (_ : t₀ ∈ O) (D : Stacks.Hilbert.HilbertFamily (Over.mk fX)
        (Over.mk (O.ι ≫ a)) (genus fX)),
      D.picardClass = Stacks.Picard.schemePullbackClass
        (Stacks.Hilbert.familyBaseChangeMap (Over.mk fX)
          (Over.homMk O.ι rfl : (Over.mk (O.ι ≫ a) : Over (Spec (.of k))) ⟶ Over.mk a)) x := by
  set fT := ((Over.pullback (Over.mk a).hom).obj (Over.mk fX)).hom
  have : IsProper fT := isProper_baseChange_hom fX a
  obtain ⟨R, _, _, ι, hι, -, ⟨y₀, hy₀⟩, hRalg⟩ := exists_chart a ⊤ t₀ trivial
  let g₁ : (Over.mk (ι ≫ a) : Over (Spec (.of k))) ⟶ Over.mk a := Over.homMk ι rfl
  let q := Stacks.Hilbert.familyBaseChangeMap (Over.mk fX) g₁
  set fR := ((Over.pullback (Over.mk (ι ≫ a)).hom).obj (Over.mk fX)).hom
  have hq : IsPullback q fR fT ι := Stacks.Hilbert.isPullback_familyBaseChangeMap (Over.mk fX) g₁
  have hRsq := isPullback_fst_baseChange_of_algebraMap fX a ι hRalg
  let LR := (Scheme.Modules.pullback q).obj (rep x)
  have hfibR : ∀ (z : Spec (.of R)) (n : ℕ),
      Module.finrank ((Spec (.of R)).residueField z) (fibreCohomology fR LR z n) =
        classFibreRank fT x (ι z) n := fun z n =>
    Stacks.FibreCohomology.finrank_fibreCohomology_eq_of_isPullback fT (rep x) q fR ι hq LR
      (Iso.refl _) z n
  obtain ⟨s, OR, hOR, hy₀OR, hnz⟩ := Stacks.TwoAffineCech.exists_section_ne_zero_on_fieldPoints
    fX U hU hUaff (pullback.fst fX (ι ≫ a)) fR hRsq LR
    (fun z => (hfibR z 1).trans (h1 _)) (fun z => (hfibR z 0).trans (h0 _)) y₀
  -- the open of `T`
  let O : T.Opens := ⟨ι.base '' OR, ι.isOpenEmbedding.isOpenMap _ hOR⟩
  have ht₀ : t₀ ∈ O := ⟨y₀, hy₀OR, hy₀⟩
  have hOι : Set.range O.ι.base ⊆ Set.range ι.base := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨z, -, rfl⟩; exact ⟨z, rfl⟩
  let lam : (O : Scheme.{u}) ⟶ Spec (.of R) := IsOpenImmersion.lift ι O.ι hOι
  have hlam : lam ≫ ι = O.ι := IsOpenImmersion.lift_fac ι O.ι hOι
  have hlamOR : ∀ w, lam w ∈ OR := fun w => by
    have hmem : O.ι w ∈ (O : Set T) := by rw [← Scheme.Opens.range_ι]; exact ⟨w, rfl⟩
    obtain ⟨z, hz, hzw⟩ : O.ι w ∈ ι.base '' OR := hmem
    have : ι z = ι (lam w) := by rw [hzw, ← Scheme.Hom.comp_apply, hlam]
    rwa [ι.isOpenEmbedding.injective this] at hz
  let g₂ : (Over.mk (O.ι ≫ a) : Over (Spec (.of k))) ⟶ Over.mk (ι ≫ a) :=
    Over.homMk lam (by
      change lam ≫ ι ≫ a = O.ι ≫ a
      rw [← Category.assoc, hlam])
  let μ := Stacks.Hilbert.familyBaseChangeMap (Over.mk fX) g₂
  set fO := ((Over.pullback (Over.mk (O.ι ≫ a)).hom).obj (Over.mk fX)).hom
  have hμ : IsPullback μ fO fR lam := Stacks.Hilbert.isPullback_familyBaseChangeMap (Over.mk fX) g₂
  let LO := (Scheme.Modules.pullback μ).obj LR
  let sO := pullbackGlobalSections μ LR s
  have hLR : Stacks.Ample.IsInvertibleModule _ LR :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback q (rep x)
  have hLO' : Stacks.Ample.IsInvertibleModule _ LO :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback μ LR
  have hLO : SheafOfModules.IsInvertible
      ((Over.pullback (Over.mk (O.ι ≫ a)).hom).obj (Over.mk fX)).left.sheaf.obj
      ((Over.pullback (Over.mk (O.ι ≫ a)).hom).obj (Over.mk fX)).left.ringCatSheaf.property LO :=
    hLO'
  have hsO : ∀ w : (O : Scheme.{u}), pullbackGlobalSections (fO.fiberι w) LO sO ≠ 0 := by
    intro w
    refine pullbackGlobalSections_ne_zero_of_comp _ μ LR s ?_
    set K := (O : Scheme.{u}).residueField w
    set φ := Spec.preimage ((O : Scheme.{u}).fromSpecResidueField w ≫ lam)
    have hφ :
        Spec.map (CommRingCat.ofHom φ.hom) = (O : Scheme.{u}).fromSpecResidueField w ≫ lam := by
      rw [CommRingCat.ofHom_hom]; exact Spec.map_preimage _
    have hker : RingHom.ker φ.hom = (lam w).asIdeal := ker_preimage_fromSpecResidueField_comp lam w
    have hsq : IsPullback (fO.fiberι w ≫ μ) (fO.fiberToSpecResidueField w) fR
        (Spec.map (CommRingCat.ofHom φ.hom)) :=
      (congrArg (fun ψ => IsPullback (fO.fiberι w ≫ μ) (fO.fiberToSpecResidueField w) fR ψ)
        hφ).mpr ((IsPullback.of_hasPullback fO _).paste_horiz hμ)
    exact hnz K φ.hom (lam w) (hlamOR w) hker _ _ hsq
  -- the zero scheme
  have hOsq : IsPullback (pullback.fst fX (O.ι ≫ a)) fO fX (O.ι ≫ a) :=
    IsPullback.of_hasPullback fX (O.ι ≫ a)
  have hfibO : ∀ (w : (O : Scheme.{u})) (n : ℕ),
      Module.finrank ((O : Scheme.{u}).residueField w) (fibreCohomology fO LO w n) =
        classFibreRank fT x (ι (lam w)) n := fun w n => by
    have : IsProper fR := isProper_baseChange_hom fX _
    rw [← hfibR]
    exact Stacks.FibreCohomology.finrank_fibreCohomology_eq_of_isPullback fR LR μ fO lam hμ LO
      (Iso.refl _) w n
  have hχ : ∀ w : (O : Scheme.{u}),
      (Module.finrank ((O : Scheme.{u}).residueField w) (fibreCohomology fO LO w 0) : ℤ) -
        Module.finrank ((O : Scheme.{u}).residueField w) (fibreCohomology fO LO w 1) =
          (genus fX : ℕ) + 1 - genus fX := fun w => by
    rw [hfibO, hfibO, h0, h1]; push_cast; ring
  have hrank := isFiniteLocallyFreeOfRank_zeroScheme fX (O.ι ≫ a) _ fO hOsq LO sO hsO
    (genus fX) hχ
  refine ⟨O, ht₀, ⟨zeroScheme _ LO sO, hrank⟩, ?_⟩
  -- the class of the divisor
  have hD := (isRelativeEffectiveCartierDivisor_zeroScheme fX (O.ι ≫ a) _ fO hOsq LO sO hsO).1
  have hreg : IsRegularSection _ _ (Stacks.Divisors.sectionsOfTop LO sO) := by
    have h := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection _ LO
      (Stacks.Divisors.sectionsOfTop LO sO)).1
    rw [Stacks.Divisors.sectionsOfTop_eval_top] at h
    exact h hD
  have eD := invertibleSheafIsoZeroSchemeOfIsRegularSection LO
    (Stacks.Divisors.sectionsOfTop LO sO) hreg
  rw [Stacks.Divisors.sectionsOfTop_eval_top] at eD
  have hcomp : μ ≫ q = Stacks.Hilbert.familyBaseChangeMap (Over.mk fX)
      (Over.homMk O.ι rfl : (Over.mk (O.ι ≫ a) : Over (Spec (.of k))) ⟶ Over.mk a) := by
    have hg : g₂ ≫ g₁ = (Over.homMk O.ι rfl :
        (Over.mk (O.ι ≫ a) : Over (Spec (.of k))) ⟶ Over.mk a) := by
      ext; exact hlam
    rw [← hg]
    unfold μ q Stacks.Hilbert.familyBaseChangeMap
    rw [pullback.map_comp]
    rfl
  set y := Stacks.Picard.schemePullbackClass (μ ≫ q) x
  obtain ⟨ey⟩ := nonempty_rep_schemePullbackClass_iso (μ ≫ q) x
  have e : rep y ≅ invertibleSheaf' (zeroScheme _ LO sO) :=
    ey ≪≫ (Scheme.Modules.pullbackComp μ q).symm.app (rep x) ≪≫ eD
  rw [← hcomp]
  exact ((Stacks.SheafOfModules.picardClass_eq_iff _ _ (invertibleSheaf' (zeroScheme _ LO sO))
    (rep y) _ (Stacks.Picard.picardRepresentative _ y).property).2 ⟨e.symm⟩).trans
    (Stacks.Picard.classOf_picardRepresentative _ y)

end Families

end Stacks.PicardCurve
