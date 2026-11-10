module

public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.UniversallyBoundedFibresComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Fibre degree bounds over a finite open cover of the source

A bound on the degrees of the fibres of a morphism of schemes may be assembled from bounds over
the members of a finite open cover of its source: the fibre over a point is covered by the
fibres of the members, and the degree of a fibre, being the dimension of its ring of global
sections, is at most the sum of the dimensions over that cover.

## Main results

* `AlgebraicGeometry.boundsFiberDegrees_of_openCover`: the sum of bounds over the members of a
  finite open cover of the source bounds the degrees of the fibres.
* `AlgebraicGeometry.Space.hasUniversallyBoundedFibers_of_finite_openCover`: the same statement
  for a morphism from a scheme to a presheaf on the big fppf site of `S`, the cover being a
  finite jointly surjective family of open subobjects of the source.
* `AlgebraicGeometry.Space.openObj` and `AlgebraicGeometry.Space.openIncl`: an open subscheme of
  the scheme underlying an object of the site, as an object of the site.

## Implementation notes

The fibre of the whole morphism is affine, which is needed to read its degree off its ring of
global sections, and this is not assumed: each member of the cover of the fibre is finite
locally free over the residue field, hence a finite discrete space, and a space with a finite
open cover by finite discrete subspaces is itself finite and discrete.

A global section of the fibre is determined by its restrictions to the members of the cover, so
the ring of global sections injects into the product of theirs; over a field this bounds its
dimension by the sum of their dimensions.

## References

* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03J4](https://stacks.math.columbia.edu/tag/03J4)
* [Stacks Project, Tag 03JL](https://stacks.math.columbia.edu/tag/03JL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Morphisms

universe u

namespace AlgebraicGeometry

/-- A scheme that is finite locally free of some rank over the spectrum of a field is a finite
discrete space: its ring of global sections is a finite-dimensional algebra over that field,
hence an Artinian ring of dimension zero. -/
@[ega "I 6.2.2" "special case", ega "I 6.4.4" "(e) ⇒ (c′) and (b)"]
private theorem finite_and_discreteTopology_of_isFiniteLocallyFreeOfRank {K : Type u} [Field K]
    {Z : Scheme.{u}} (p : Z ⟶ Spec (.of K)) (r : ℕ)
    (h : IsFiniteLocallyFreeOfRank p r) : Finite Z ∧ DiscreteTopology Z := by
  have : IsAffineHom p := h.toIsAffineHom
  have : IsAffine Z := isAffine_of_isAffineHom p
  let _ : Algebra K ↑Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop).hom.toAlgebra
  obtain ⟨-, hfin, -⟩ := (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq p r).mp h
  have : IsArtinianRing ↑Γ(Z, ⊤) := IsArtinianRing.of_finite K ↑Γ(Z, ⊤)
  have hdim : Ring.KrullDimLE 0 ↑Γ(Z, ⊤) :=
    Ring.krullDimLE_zero_iff.mpr fun I hI ↦ (IsArtinianRing.isPrime_iff_isMaximal I).mp hI
  have hdisc : DiscreteTopology (PrimeSpectrum ↑Γ(Z, ⊤)) :=
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero.mpr ⟨inferInstance, hdim⟩
  have : Finite (Spec Γ(Z, ⊤) : Scheme.{u}) := inferInstanceAs (Finite (PrimeSpectrum ↑Γ(Z, ⊤)))
  exact ⟨Finite.of_equiv _ Z.isoSpec.hom.homeomorph.toEquiv.symm,
    Z.isoSpec.hom.homeomorph.discreteTopology_iff.mpr hdisc⟩

/-- A scheme with a finite open cover by finite discrete subspaces is finite and discrete. -/
private theorem finite_and_discreteTopology_of_openCover {Z : Scheme.{u}} (𝒱 : Z.OpenCover)
    [Finite 𝒱.I₀] (hfin : ∀ i, Finite (𝒱.X i)) (hdisc : ∀ i, DiscreteTopology (𝒱.X i)) :
    Finite Z ∧ DiscreteTopology Z := by
  refine ⟨?_, ⟨eq_bot_of_singletons_open fun z ↦ ?_⟩⟩
  · have huniv : (Set.univ : Set Z).Finite := by
      rw [← 𝒱.iUnion_range]
      exact Set.finite_iUnion fun i ↦ have := hfin i; Set.finite_range _
    exact Set.finite_univ_iff.mp huniv
  · obtain ⟨i, w, hw⟩ := 𝒱.exists_eq z
    have hw' : IsOpen ({w} : Set (𝒱.X i)) := have := hdisc i; isOpen_discrete _
    have himg := (𝒱.f i).isOpenEmbedding.isOpenMap _ hw'
    rwa [Set.image_singleton, hw] at himg

/-- The dimension of the ring of global sections of a scheme is at most the sum of the
dimensions over a finite open cover: a global section is determined by its restrictions. -/
private theorem finite_and_finrank_le_sum_of_openCover {K : Type u} [Field K] {Z : Scheme.{u}}
    (𝒱 : Z.OpenCover) [Fintype 𝒱.I₀] [Module K ↑Γ(Z, ⊤)] [∀ i, Module K ↑Γ(𝒱.X i, ⊤)]
    (m : 𝒱.I₀ → ℕ) (hfinite : ∀ i, Module.Finite K ↑Γ(𝒱.X i, ⊤))
    (hbound : ∀ i, Module.finrank K ↑Γ(𝒱.X i, ⊤) ≤ m i)
    (hcompat : ∀ i (a : K) (s : ↑Γ(Z, ⊤)), (𝒱.f i).appTop (a • s) = a • (𝒱.f i).appTop s) :
    Module.Finite K ↑Γ(Z, ⊤) ∧ Module.finrank K ↑Γ(Z, ⊤) ≤ ∑ i, m i := by
  let L : ↑Γ(Z, ⊤) →ₗ[K] ∀ i, ↑Γ(𝒱.X i, ⊤) :=
    { toFun := fun s i ↦ (𝒱.f i).appTop s
      map_add' := by intro s s'; ext i; simp
      map_smul' := by intro a s; ext i; exact hcompat i a s }
  have hL : Function.Injective L := fun s s' hss' ↦
    𝒱.ext_elem s s' fun i ↦ congrFun hss' i
  have _ : ∀ i, Module.Finite K ↑Γ(𝒱.X i, ⊤) := hfinite
  refine ⟨Module.Finite.of_injective L hL, ?_⟩
  calc Module.finrank K ↑Γ(Z, ⊤)
      ≤ Module.finrank K (∀ i, ↑Γ(𝒱.X i, ⊤)) := LinearMap.finrank_le_finrank_of_injective hL
    _ = ∑ i, Module.finrank K ↑Γ(𝒱.X i, ⊤) := by
      simpa using Module.finrank_pi_fintype (R := K) (M := fun i : 𝒱.I₀ ↦ ↑Γ(𝒱.X i, ⊤))
    _ ≤ ∑ i, m i := Finset.sum_le_sum fun i _ ↦ hbound i

/-- Bounds on the degrees of the fibres over the members of a finite open cover of the source of
a morphism of schemes add up to a bound on the degrees of its fibres. -/
theorem boundsFiberDegrees_of_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : X.OpenCover)
    [hUfin : Fintype 𝒰.I₀] (m : 𝒰.I₀ → ℕ)
    (hbnd : ∀ i, BoundsFiberDegrees (𝒰.f i ≫ f) (m i : ℤ)) :
    BoundsFiberDegrees f ((∑ i, m i : ℕ) : ℤ) := by
  intro y
  let K := Y.residueField y
  let q := Y.fromSpecResidueField y
  let p := f.fiberToSpecResidueField y
  let 𝒱 : (f.fiber y).OpenCover := Scheme.Pullback.openCoverOfLeft 𝒰 f q
  have hVfin : Fintype 𝒱.I₀ := ‹Fintype 𝒰.I₀›
  let pi : ∀ i : 𝒱.I₀, 𝒱.X i ⟶ Spec K := fun i ↦ (𝒰.f i ≫ f).fiberToSpecResidueField y
  have hproj : ∀ i : 𝒱.I₀, 𝒱.f i ≫ p = pi i := by
    intro i
    change pullback.map (𝒰.f i ≫ f) q f q (𝒰.f i) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
      pullback.snd f q = pullback.snd (𝒰.f i ≫ f) q
    rw [pullback.map, pullback.lift_snd, Category.comp_id]
  have hrank : ∀ i : 𝒱.I₀, ∃ r : ℕ, r ≤ m i ∧ IsFiniteLocallyFreeOfRank (pi i) r := fun i ↦
    (hbnd i y).imp fun _ h ↦ ⟨by exact_mod_cast h.1, h.2⟩
  -- The fibre is finite and discrete, hence affine.
  have hfd : ∀ i : 𝒱.I₀, Finite (𝒱.X i) ∧ DiscreteTopology (𝒱.X i) := fun i ↦
    (hrank i).elim fun r h ↦ finite_and_discreteTopology_of_isFiniteLocallyFreeOfRank (pi i) r h.2
  obtain ⟨hZfinite, hZdisc⟩ :=
    finite_and_discreteTopology_of_openCover 𝒱 (fun i ↦ (hfd i).1) fun i ↦ (hfd i).2
  have _ : Finite ↥(f.fiber y) := hZfinite
  have _ : DiscreteTopology ↥(f.fiber y) := hZdisc
  have _ : IsAffine (f.fiber y) := inferInstance
  have hpaff : IsAffineHom p := inferInstance
  -- The degree of the fibre is the dimension of its ring of global sections.
  let _ : Algebra ↑K ↑Γ(f.fiber y, ⊤) := ((Scheme.ΓSpecIso K).inv ≫ p.appTop).hom.toAlgebra
  let _ : ∀ i : 𝒱.I₀, Algebra ↑K ↑Γ(𝒱.X i, ⊤) := fun i ↦
    ((Scheme.ΓSpecIso K).inv ≫ (pi i).appTop).hom.toAlgebra
  have hdim : ∀ i : 𝒱.I₀, Module.Finite ↑K ↑Γ(𝒱.X i, ⊤) ∧
      Module.finrank ↑K ↑Γ(𝒱.X i, ⊤) ≤ m i := by
    intro i
    obtain ⟨r, hr, hrk⟩ := hrank i
    obtain ⟨-, hfin, heq⟩ :=
      (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq (pi i) r).mp hrk
    exact ⟨hfin, heq.le.trans hr⟩
  have hcompat : ∀ (i : 𝒱.I₀) (a : ↑K) (s : ↑Γ(f.fiber y, ⊤)),
      (𝒱.f i).appTop (a • s) = a • (𝒱.f i).appTop s := by
    intro i a s
    have harrow : (Scheme.ΓSpecIso K).inv ≫ p.appTop ≫ (𝒱.f i).appTop =
        (Scheme.ΓSpecIso K).inv ≫ (pi i).appTop := by
      rw [← Scheme.Hom.comp_appTop, hproj i]
    have hring := congrArg CommRingCat.Hom.hom harrow
    have ha := congrFun (congrArg (fun φ : K →+* Γ(𝒱.X i, ⊤) ↦ (φ : K → Γ(𝒱.X i, ⊤))) hring) a
    change (𝒱.f i).appTop.hom (((Scheme.ΓSpecIso K).inv ≫ p.appTop).hom a * s) =
      ((Scheme.ΓSpecIso K).inv ≫ (pi i).appTop).hom a * (𝒱.f i).appTop.hom s
    rw [map_mul]
    exact congrArg (· * (𝒱.f i).appTop.hom s) (by simpa using ha)
  obtain ⟨hfin, hle⟩ := finite_and_finrank_le_sum_of_openCover 𝒱 m
    (fun i ↦ (hdim i).1) (fun i ↦ (hdim i).2) hcompat
  have hsum : (∑ i : 𝒱.I₀, m i) = ∑ i : 𝒰.I₀, m i :=
    @Fintype.sum_equiv 𝒱.I₀ 𝒰.I₀ ℕ hVfin hUfin _ (Equiv.refl _) m m fun _ ↦ rfl
  rw [hsum] at hle
  refine ⟨Module.finrank ↑K ↑Γ(f.fiber y, ⊤), by exact_mod_cast hle, ?_⟩
  exact (isFiniteLocallyFreeOfRank_iff_finrank_sections_eq p _).mpr ⟨hpaff, hfin, rfl⟩

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 000R (3)** in the site: an open subscheme of the scheme underlying an object of the
big fppf site of `S` is again an object of the site, with the structure morphism inherited. -/
noncomputable def openObj (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) : BigFppfOver B S hS :=
  Over.mk (⟨O.ι ≫ U.hom.hom⟩ :
    B.obj (Scheme.size_lt_of_isOpenImmersion O.ι U.left.property) ⟶ B.obj hS)

/-- The inclusion of an open subobject. -/
noncomputable def openIncl (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) : openObj B S hS U O ⟶ U :=
  Over.homMk ⟨O.ι⟩ rfl

/-- The underlying scheme of an open subobject is the open subscheme. -/
theorem toScheme_obj_openObj (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).obj (openObj B S hS U O) = O.toScheme := rfl

/-- The underlying morphism of schemes of the inclusion of an open subobject is the canonical
open immersion. -/
theorem toScheme_map_openIncl (U : BigFppfOver B S hS)
    (O : ((BigFppfOver.toScheme B S hS).obj U).Opens) :
    (BigFppfOver.toScheme B S hS).map (openIncl B S hS U O) = O.ι := rfl

/-- Universally bounded fibres are detected on a finite jointly surjective family of open
subobjects of the source: if each member of such a family has universally bounded fibres over a
presheaf `X`, then so does the whole object.

The fibre of the whole morphism over a field-valued point is covered by the fibres of the
members, which are its open subschemes, and the degrees of the fibres add up over that cover. -/
theorem hasUniversallyBoundedFibers_of_finite_openCover
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {W : BigFppfOver B S hS}
    (Ψ : yoneda.obj W ⟶ X) (hΨ : yoneda.relativelyRepresentable Ψ)
    {L : Type u} [Finite L] (V : L → BigFppfOver B S hS) (σ : ∀ l, V l ⟶ W)
    (hopen : ∀ l, IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (σ l)))
    (hsurj : ∀ w : (BigFppfOver.toScheme B S hS).obj W,
      ∃ (l : L) (z : (BigFppfOver.toScheme B S hS).obj (V l)),
        (BigFppfOver.toScheme B S hS).map (σ l) z = w)
    (hbnd : ∀ l, HasUniversallyBoundedFibers B S hS (V l) (yoneda.map (σ l) ≫ Ψ)) :
    HasUniversallyBoundedFibers B S hS W Ψ := by
  classical
  have hLfin : Fintype L := Fintype.ofFinite L
  choose n hn using hbnd
  refine ⟨((∑ l, (n l).toNat : ℕ) : ℤ), fun k _ A hA ξ ↦ ?_⟩
  set Fs := BigFppfOver.toScheme B S hS with hFs
  set cQ : hΨ.pullback ξ ⟶ W := hΨ.fst' ξ with hcQ
  set pQ : hΨ.pullback ξ ⟶ A := hΨ.snd ξ with hpQ
  have hQsq : IsPullback (yoneda.map cQ) (yoneda.map pQ) Ψ ξ := hΨ.isPullback' ξ
  -- The pieces of the fibre: base change the family along the fibre's map to `W`.
  have hRsq : ∀ l, IsPullback (Limits.pullback.fst (σ l) cQ) (Limits.pullback.snd (σ l) cQ)
      (σ l) cQ := fun l ↦ IsPullback.of_hasPullback _ _
  have hbopen : ∀ l, IsOpenImmersion (Fs.map (Limits.pullback.snd (σ l) cQ)) := fun l ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @IsOpenImmersion) ((hRsq l).map Fs) (hopen l)
  have hbsurj : ∀ x : Fs.obj (hΨ.pullback ξ),
      ∃ l z, Fs.map (Limits.pullback.snd (σ l) cQ) z = x := by
    intro x
    obtain ⟨l, z, hz⟩ := hsurj (Fs.map cQ x)
    obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback ((hRsq l).map Fs) z x hz
    exact ⟨l, w, hw⟩
  let 𝒬 : (Fs.obj (hΨ.pullback ξ)).OpenCover :=
    Scheme.Cover.mkOfCovers L (fun l ↦ Fs.obj (Limits.pullback (σ l) cQ))
      (fun l ↦ Fs.map (Limits.pullback.snd (σ l) cQ)) hbsurj fun l ↦ hbopen l
  have hQfin : Fintype 𝒬.I₀ := hLfin
  -- Each piece of the fibre is a fibre of the corresponding member of the family.
  have hpiece : ∀ l, BoundsFiberDegrees
      (Fs.map (Limits.pullback.snd (σ l) cQ) ≫ Fs.map pQ) (((n l).toNat : ℕ) : ℤ) := by
    intro l
    obtain ⟨V', p', i', r', hr', hrank', hsq'⟩ := hn l k A hA ξ
    have hpaste : IsPullback (yoneda.map (Limits.pullback.fst (σ l) cQ))
        (yoneda.map (Limits.pullback.snd (σ l) cQ ≫ pQ)) (yoneda.map (σ l) ≫ Ψ) ξ := by
      rw [Functor.map_comp]
      exact IsPullback.paste_vert ((hRsq l).map yoneda) hQsq
    obtain ⟨ι, hιiso, hι⟩ : ∃ ι : Limits.pullback (σ l) cQ ⟶ V', IsIso ι ∧
        Limits.pullback.snd (σ l) cQ ≫ pQ = ι ≫ p' := by
      obtain ⟨m, hmiso, hm⟩ : ∃ m : yoneda.obj (Limits.pullback (σ l) cQ) ⟶ yoneda.obj V',
          IsIso m ∧ m ≫ yoneda.map p' = yoneda.map (Limits.pullback.snd (σ l) cQ ≫ pQ) :=
        ⟨(hsq'.isoIsPullback _ _ hpaste).inv, inferInstance,
          hsq'.isoIsPullback_inv_snd _ _ hpaste⟩
      refine ⟨yoneda.preimage m, ?_, ?_⟩
      · have : IsIso (yoneda.map (yoneda.preimage m)) := by rwa [yoneda.map_preimage]
        exact Yoneda.fullyFaithful.isIso_of_isIso_map _
      · apply yoneda.map_injective
        refine hm.symm.trans ?_
        rw [Functor.map_comp, yoneda.map_preimage]
    have hrank : IsFiniteLocallyFreeOfRank
        (Fs.map (Limits.pullback.snd (σ l) cQ ≫ pQ)) r' := by
      have := hιiso
      rw [hι, Functor.map_comp]
      exact MorphismProperty.RespectsIso.precomp (IsFiniteLocallyFreeOfRank.property r')
        (Fs.map ι) (Fs.map p') hrank'
    rw [← Functor.map_comp]
    intro y
    obtain ⟨r, hr, hrk⟩ := boundsFiberDegrees_of_isFiniteLocallyFreeOfRank
      (Fs.map (Limits.pullback.snd (σ l) cQ ≫ pQ)) r' y
    exact ⟨r, hr.trans ((by exact_mod_cast hr' : (r' : ℤ) ≤ n l).trans (Int.self_le_toNat _)), hrk⟩
  -- The degrees add up over the cover, and over a field spectrum a bound is a rank.
  have hsum : (∑ i : 𝒬.I₀, (n i).toNat) = ∑ l : L, (n l).toNat :=
    @Fintype.sum_equiv 𝒬.I₀ L ℕ hQfin hLfin _ (Equiv.refl _) _ _ fun _ ↦ rfl
  have hfib : BoundsFiberDegrees (Fs.map pQ) ((∑ l, (n l).toNat : ℕ) : ℤ) := by
    have h0 := boundsFiberDegrees_of_openCover (Fs.map pQ) 𝒬 (fun l ↦ (n l).toNat) hpiece
    rwa [hsum] at h0
  have hiso : IsPullback (𝟙 (Fs.obj (hΨ.pullback ξ))) (Fs.map pQ ≫ hA.hom)
      (Fs.map pQ) hA.inv := IsPullback.of_horiz_isIso (CommSq.mk (by simp))
  obtain ⟨r, hr, hrank⟩ := exists_rank_le_of_boundsFiberDegrees_of_specTarget _
    (boundsFiberDegrees_of_isPullback hiso hfib)
  exact ⟨hΨ.pullback ξ, pQ, yoneda.map cQ, r, hr,
    ((IsFiniteLocallyFreeOfRank.property r).cancel_right_of_respectsIso _ hA.hom).mp hrank,
    hQsq⟩

end Space

end AlgebraicGeometry

end
