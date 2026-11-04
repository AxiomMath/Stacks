module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBundle.Classes
public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeBasis
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishingFieldExtension
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RepresentedPicardZero
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CurveBridges
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.AsymptoticRiemannRoch

/-!
# A basis of sections of the translated universal class near a point of `Pic⁰`

Let `X` be a smooth proper geometrically irreducible curve of genus `g` over a field `k` with a
rational point `σ`, let `A` represent `Pic⁰_{X/k,σ}`, and let `θ` be a class of degree
`d ≥ 2g - 1`. The translated universal class `ℒ` on `X_A` has degree `d` on every fibre, so has no
higher cohomology on the fibres and `d + 1 - g` independent sections there. By cohomology and base
change in degree `0`, every point `y ∈ A` has an affine neighbourhood `W` and `g ∈ Γ(W, 𝒪)` with
`y ∈ D(g)`, and sections `e₁, …, e_{d+1-g}` of `ℒ|_{X_W}` whose pullbacks form a basis of the
sections of the pullback of `ℒ` over every affine scheme mapping to `D(g)`.

## Main results

* `Stacks.RigidifiedPicard.relativeInvertibleDegreeHomAt_abelTranslatedClass` — `ℒ` has degree
  `d` on every fibre.
* `Stacks.RigidifiedPicard.exists_abelSectionBasis` — the basis.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.RigidifiedPicard

section General

variable {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] [IsProper f]
  [SmoothOfRelativeDimension 1 f] [LocallyOfFiniteType f]
  (hdim : ∀ s : S, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (A : Grp (Over S)) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : S, relativeInvertibleDegreeHomAt f hdim s θ = d)

include hθ in
/-- **The translated universal class has degree `d` on every fibre of `X_A ⟶ A`.** -/
theorem relativeInvertibleDegreeHomAt_abelTranslatedClass (w : A.X.left) :
    relativeInvertibleDegreeHomAt (bcProj f A.X) (topologicalKrullDim_fiber_bcProj_le f hdim A.X) w
      (abelTranslatedClass f hdim σ hσ A e θ) = d := by
  have h0 := (mem_groupZero_iff f hdim σ hσ A.X _).1
    (Multiplicative.toAdd (abelUniversalElement f hdim σ hσ A e)).2 w
  rw [degree_apply] at h0
  rw [abelTranslatedClass, map_add, relativeInvertibleDegreeHomAt_fst f hdim θ A.X w, hθ]
  exact (congrArg (· + (d : ℤ)) h0).trans (zero_add _)

end General

section Field

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]

/-- The pullback of an invertible module along a morphism of schemes has the pulled-back class. -/
theorem picardClass_pullback {Y Z : Scheme.{u}} (h : Y ⟶ Z) (L : Z.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf
      (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) L)
    (hL' : Stacks.SheafOfModules.IsInvertible Y.presheaf
      (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace) ((Scheme.Modules.pullback h).obj L)) :
    Stacks.SheafOfModules.picardClass Y.presheaf
        (Stacks.RingedSpace.structureIsSheaf Y.toRingedSpace)
        ((Scheme.Modules.pullback h).obj L) hL' =
      Stacks.Picard.schemePullbackClass h
        (Stacks.SheafOfModules.picardClass Z.presheaf
          (Stacks.RingedSpace.structureIsSheaf Z.toRingedSpace) L hL) :=
  (Stacks.Picard.pullbackClass_classOf h.toLRSHom.toShHom L hL).symm

/-- **No higher cohomology and `d + 1 - g` sections on a fibre.** Let `T` be a `k`-scheme, `F` an
invertible module on `X_T` of degree `d ≥ 2g - 1` at the image of a field point `s : Spec K ⟶ T`.
On the fibre `X_K` of `X_T` over `s`, the pullback of `F` has no cohomology in positive degrees and
a space of global sections of dimension `d + 1 - g`. -/
theorem fibre_cohomology_of_degree {T : Over (Spec (.of k))} {K : Type u} [Field K] [Algebra k K]
    {Xp : Scheme.{u}} (gp : Xp ⟶ bc f T) (fp : Xp ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ T.left)
    (hsq : IsPullback gp fp (bcProj f T) s)
    (hs : s ≫ T.hom = Spec.map (CommRingCat.ofHom (algebraMap k K)))
    (hdim : ∀ x : Spec (.of k), topologicalKrullDim ↥(f.fiber x) ≤ 1)
    (F : (bc f T).Modules)
    (hF : Stacks.SheafOfModules.IsInvertible (bc f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (bc f T).toRingedSpace) F)
    {d : ℕ} (hd : 2 * (genus f : ℤ) - 1 ≤ d)
    (hdeg : ∀ t : Spec (.of K), relativeInvertibleDegreeHomAt (bcProj f T)
      (topologicalKrullDim_fiber_bcProj_le f hdim T) (s t)
      (Stacks.SheafOfModules.picardClass _ _ F hF) = d) :
    (∀ i : ℕ, 0 < i → IsZero (cohomologyOverField K fp ((Scheme.Modules.pullback gp).obj F) i)) ∧
      (Module.finrank K (cohomologyOverField K fp ((Scheme.Modules.pullback gp).obj F) 0) : ℤ) =
        d + 1 - genus f := by
  have hbig : IsPullback (gp ≫ pullback.fst f T.hom) fp f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [← hs]
    exact hsq.paste_horiz (IsPullback.of_hasPullback f T.hom)
  have : IsProper fp := MorphismProperty.of_isPullback hbig ‹IsProper f›
  have hdimX : topologicalKrullDim X ≤ 1 :=
    AlgebraicGeometry.topologicalKrullDim_le_one_of_smoothOfRelativeDimension f
  have hdim' : topologicalKrullDim Xp ≤ 1 := by
    rwa [topologicalKrullDim_baseChange k K _ fp f hbig]
  have hM := Stacks.Modules.isInvertible_pullback gp F
  have hdeg' : invertibleCurveDegreeHom K fp hdim'
      (Stacks.SheafOfModules.picardClass _ _ ((Scheme.Modules.pullback gp).obj F) hM) = d := by
    have hfib : ∀ t, topologicalKrullDim ↥(fp.fiber t) ≤ 1 := fun t => by
      rwa [topologicalKrullDim_fiber_spec fp t]
    have t : Spec (.of K) := show PrimeSpectrum K from IsLocalRing.closedPoint K
    rw [← relativeInvertibleDegreeHomAt_eq_invertibleCurveDegreeHom fp hfib hdim' t,
      picardClass_pullback gp F hF hM]
    exact (relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback hsq
        (topologicalKrullDim_fiber_bcProj_le f hdim T) hfib t _).trans (hdeg t)
  obtain ⟨h1, h0⟩ := AlgebraicGeometry.isZero_cohomologyOverField_one_and_finrank_zero_of_baseChange
    k f (gp ≫ pullback.fst f T.hom) fp hbig hdim' _ hM (by rwa [hdeg'])
  refine ⟨fun i hi => ?_, by rw [h0, hdeg']⟩
  rcases i with _ | _ | i
  · omega
  · exact h1
  · exact isZero_cohomologyOverField_of_topologicalKrullDim_le K fp _ (d := 1) hdim' (by omega)

end Field

section Basis

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
  [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
  (hdim : ∀ s : Spec (.of k), topologicalKrullDim ↥(f.fiber s) ≤ 1)
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
  (A : Grp (Over (Spec (.of k)))) (e : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
  (θ : Stacks.Picard.ofScheme X) {d : ℕ}
  (hθ : ∀ s : Spec (.of k), relativeInvertibleDegreeHomAt f hdim s θ = d)

include hθ in
/-- On the base change of `X` to an open `W ⊆ A`, the restriction of the translated universal
class to the fibre over a field point of `W` has no higher cohomology and `d + 1 - g` sections. -/
theorem fibre_cohomology_abelTranslatedClass (hd : 2 * (genus f : ℤ) - 1 ≤ d) (W : A.X.left.Opens)
    {K : Type u} [Field K] {Xp : Scheme.{u}} (gp : Xp ⟶ bc f (Over.mk (W.ι ≫ A.X.hom)))
    (fp : Xp ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ W.toScheme)
    (hsq : IsPullback gp fp (bcProj f (Over.mk (W.ι ≫ A.X.hom))) s) :
    letI : Algebra k K := (Spec.preimage (s ≫ W.ι ≫ A.X.hom)).hom.toAlgebra
    (∀ i : ℕ, 0 < i → IsZero (cohomologyOverField K fp ((Scheme.Modules.pullback gp).obj
      ((Scheme.Modules.pullback (bcMap f (Over.homMk W.ι rfl : Over.mk (W.ι ≫ A.X.hom) ⟶ A.X))).obj
        (Stacks.Picard.picardRepresentative (bc f A.X).toRingedSpace
          (abelTranslatedClass f hdim σ hσ A e θ)).obj)) i)) ∧
      (Module.finrank K (cohomologyOverField K fp ((Scheme.Modules.pullback gp).obj
      ((Scheme.Modules.pullback (bcMap f (Over.homMk W.ι rfl : Over.mk (W.ι ≫ A.X.hom) ⟶ A.X))).obj
        (Stacks.Picard.picardRepresentative (bc f A.X).toRingedSpace
          (abelTranslatedClass f hdim σ hσ A e θ)).obj)) 0) : ℤ) = d + 1 - genus f := by
  let : Algebra k K := (Spec.preimage (s ≫ W.ι ≫ A.X.hom)).hom.toAlgebra
  set ι : Over.mk (W.ι ≫ A.X.hom) ⟶ A.X := Over.homMk W.ι rfl
  set L := Stacks.Picard.picardRepresentative (bc f A.X).toRingedSpace
    (abelTranslatedClass f hdim σ hσ A e θ)
  have := L.property
  have hF := Stacks.Modules.isInvertible_pullback (bcMap f ι) L.obj
  refine fibre_cohomology_of_degree f gp fp s hsq ?_ hdim _ hF hd fun t => ?_
  · show s ≫ W.ι ≫ A.X.hom = _
    exact (Spec.map_preimage _).symm
  · rw [picardClass_pullback (bcMap f ι) L.obj L.property hF,
      Stacks.Picard.classOf_picardRepresentative,
      relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback (bcMap_isPullback_proj f ι)
        (topologicalKrullDim_fiber_bcProj_le f hdim A.X)]
    exact relativeInvertibleDegreeHomAt_abelTranslatedClass f hdim σ hσ A e θ hθ _

/-- **The dimension of the global sections over a field, from a basis.** If the sums
`∑ cᵢ • sᵢ` with coefficients in `Γ(Spec K, 𝒪)` are a bijection onto `Γ(Y, M)`, then
`dim_K H⁰(Y, M) = n`. -/
theorem finrank_cohomologyOverField_zero_eq_of_bijective {K : Type u} [Field K] {Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of K)) (M : Y.Modules) {n : ℕ} (s : Fin n → Γ(M, ⊤))
    (hbij : Function.Bijective (fun c : Fin n → Γ(Spec (.of K), ⊤) =>
      ∑ i, (p.appTop (c i) : Γ(Y, ⊤)) • s i)) :
    Module.finrank K (cohomologyOverField K p M 0) = n := by
  rw [← finrank_globalSectionsOverField]
  let ψ : K →+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom
  have hψ : Function.Bijective ψ :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv
  let Φ : (Fin n → K) →ₗ[K] globalSectionsOverField K p M :=
    { toFun := fun c => (∑ i, (p.appTop (ψ (c i)) : Γ(Y, ⊤)) • s i : Γ(M, ⊤))
      map_add' := fun c c' => by
        simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
        rfl
      map_smul' := fun a c => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_smul, RingHom.id_apply]
        rw [← Finset.smul_sum]
        have happ : ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appLE ⊤ ⊤ (by simp)).hom a =
            p.appTop (ψ a) :=
          congrArg (fun φ : Γ(Spec (.of K), ⊤) ⟶ Γ(Y, ⊤) => φ.hom (ψ a))
            (Scheme.Hom.appLE_eq_app p (U := ⊤))
        show _ = ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appLE ⊤ ⊤ (by simp)).hom a •
          (∑ x, (p.appTop (ψ (c x)) : Γ(Y, ⊤)) • s x : Γ(M, ⊤))
        rw [happ] }
  have hΦ : Function.Bijective Φ := hbij.comp hψ.comp_left
  rw [← (LinearEquiv.ofBijective Φ hΦ).finrank_eq, Module.finrank_fin_fun]

include hθ in
/-- **A basis of sections of the translated universal class near a point of `Pic⁰`.** For
`d ≥ 2g - 1` and `y ∈ A`, there are an affine open `W ∋ y`, `g ∈ Γ(W, 𝒪)` with `y ∈ D(g)`, and
sections `e₁, …, e_{d+1-g}` of the translated universal class on `X_W` whose pullbacks form a
basis of the sections of its pullback over every affine scheme mapping into `D(g)`. -/
theorem exists_abelSectionBasis [LocallyOfFiniteType A.X.hom] (hd : 2 * (genus f : ℤ) - 1 ≤ d)
    (y : A.X.left) :
    ∃ (W : A.X.left.Opens) (_ : IsAffineOpen W) (hyW : y ∈ W) (g : Γ(W, ⊤))
      (eW : Fin (d + 1 - genus f) → Γ((Scheme.Modules.pullback (bcMap f
        (Over.homMk W.ι rfl : Over.mk (W.ι ≫ A.X.hom) ⟶ A.X))).obj
          (Stacks.Picard.picardRepresentative (bc f A.X).toRingedSpace
            (abelTranslatedClass f hdim σ hσ A e θ)).obj, ⊤)),
      (⟨y, hyW⟩ : W.toScheme) ∈ W.toScheme.basicOpen g ∧
      ∀ {T' Y' : Scheme.{u}} [IsAffine T'] (h : T' ⟶ (Over.mk (W.ι ≫ A.X.hom)).left),
        Set.range h ⊆ (W.toScheme.basicOpen g : Set W.toScheme) →
        ∀ (p' : Y' ⟶ T') (g' : Y' ⟶ bc f (Over.mk (W.ι ≫ A.X.hom))),
          IsPullback g' p' (bcProj f (Over.mk (W.ι ≫ A.X.hom))) h →
          Function.Bijective (fun c : Fin (d + 1 - genus f) → Γ(T', ⊤) =>
            ∑ i, (p'.appTop (c i) : Γ(Y', ⊤)) • pullbackGlobalSections g' _ (eW i)) := by
  obtain ⟨W, hW, hyW, -⟩ : ∃ W : A.X.left.Opens, W ∈ A.X.left.affineOpens ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      A.X.left.isBasis_affineOpens) (show y ∈ (⊤ : A.X.left.Opens) from trivial)
  have hWa : IsAffineOpen W := hW
  have : IsAffine (Over.mk (W.ι ≫ A.X.hom)).left := hWa
  have : IsLocallyNoetherian (Over.mk (W.ι ≫ A.X.hom)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (W.ι ≫ A.X.hom)
  set ι : Over.mk (W.ι ≫ A.X.hom) ⟶ A.X := Over.homMk W.ι rfl
  set L := Stacks.Picard.picardRepresentative (bc f A.X).toRingedSpace
    (abelTranslatedClass f hdim σ hσ A e θ)
  have := L.property
  have hF := Stacks.Modules.isInvertible_pullback (bcMap f ι) L.obj
  have hFa : AlgebraicGeometry.SheafOfModules.IsInvertible
      (bc f (Over.mk (W.ι ≫ A.X.hom))).presheaf
      (bc f (Over.mk (W.ι ≫ A.X.hom))).ringCatSheaf.2
      ((Scheme.Modules.pullback (bcMap f ι)).obj L.obj) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1 hF
  obtain ⟨g, n, eS, hy, hbij⟩ :=
    AlgebraicGeometry.ProperFlatGlobalSections.exists_basicOpen_bijective_sum_pullbackGlobalSections
      (bcProj f (Over.mk (W.ι ≫ A.X.hom))) ((Scheme.Modules.pullback (bcMap f ι)).obj L.obj)
      (⟨y, hyW⟩ : W.toScheme) (fun x _ Xp fp gp hpull i hi => by
        have := ModuleCat.subsingleton_of_isZero
          ((fibre_cohomology_abelTranslatedClass f hdim σ hσ A e θ hθ hd W gp fp _ hpull).1 i hi)
        exact this)
  -- the rank is `d + 1 - g`, read on the fibre over `y`
  have hn : n = d + 1 - genus f := by
    set y₀ : W.toScheme := ⟨y, hyW⟩
    let h := W.toScheme.fromSpecResidueField y₀
    have hsq := IsPullback.of_hasPullback (bcProj f (Over.mk (W.ι ≫ A.X.hom))) h
    have hrange : Set.range h ⊆ W.toScheme.basicOpen g := by
      show Set.range (W.toScheme.fromSpecResidueField y₀) ⊆ _
      rw [Scheme.range_fromSpecResidueField]
      exact Set.singleton_subset_iff.mpr hy
    have hc := (fibre_cohomology_abelTranslatedClass f hdim σ hσ A e θ hθ hd W
      (pullback.fst _ h) (pullback.snd _ h) h hsq).2
    rw [finrank_cohomologyOverField_zero_eq_of_bijective (pullback.snd _ h) _ _
      (hbij h hrange _ _ hsq)] at hc
    omega
  subst hn
  exact ⟨W, hWa, hyW, g, eS, hy, fun h hr p' g' hsq => hbij h hr p' g' hsq⟩

end Basis

end Stacks.RigidifiedPicard

end
