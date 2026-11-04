module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Topology.Inseparable
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.PointFactorization

/-!
# Factoring a morphism through a set of points

Let `E` be a set of points of a locally Noetherian scheme `X`, with no nontrivial
specializations between its elements. A morphism from a reduced scheme whose pointwise image is
contained in `E` factors through the coproduct of the spectra of the residue fields at the
points of `E`.

## Main results

* `AlgebraicGeometry.exists_factorization_through_residueFields` gives the factorization through
  the coproduct of the points in `E`.

## Implementation notes

The point scheme attached to `x : X` is represented by `Spec(κ(x))`, and the morphism from the
coproduct is the categorical coproduct descendent of the canonical residue-field morphisms. The
image condition is stated pointwise using the underlying continuous map of the scheme morphism.
Absence of nontrivial specializations is Mathlib's `Specializes` relation `· ⤳ ·`.

The argument is local on the source: on an affine chart the image is finite, because a
Noetherian ring has finitely many minimal primes, and the finite case is settled by factoring
each component through its point and gluing. The glueing is legitimate because the morphism from
the coproduct of residue-field points is a monomorphism.

## References

* [Stacks Project, Tag 0H1N](https://stacks.math.columbia.edu/tag/0H1N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A ring map into which no two primes of the source contract to specializing points of an
antichain has finite image on spectra, when the source is Noetherian. -/
private lemma finite_range_comap_of_specializes_antichain
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    (φ : R →+* S) (E : Set (PrimeSpectrum R))
    (hE : ∀ x x' : E, x.1 ⤳ x'.1 → x.1 = x'.1)
    (hf : ∀ q : PrimeSpectrum S, PrimeSpectrum.comap φ q ∈ E) :
    (Set.range (PrimeSpectrum.comap φ)).Finite := by
  let A := φ.range
  let f₁ : R →+* A := φ.rangeRestrict
  let f₂ : A →+* S := φ.range.subtype
  have hcomp : f₂.comp f₁ = φ := by ext x; rfl
  have : IsNoetherianRing A := isNoetherianRing_range φ
  have : Finite {p // p ∈ minimalPrimes A} :=
    Set.finite_coe_iff.mp (minimalPrimes.finite_of_isNoetherianRing A)
  let g : {p // p ∈ minimalPrimes A} → PrimeSpectrum R := fun p ↦
    PrimeSpectrum.comap f₁ ⟨p.1, p.2.isPrime⟩
  refine (Set.finite_range g).subset ?_
  rintro _ ⟨q, rfl⟩
  let q' := PrimeSpectrum.comap f₂ q
  obtain ⟨p, hp, hple⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := q'.asIdeal) bot_le
  have hf₂ : Function.Injective f₂ := fun _ _ h ↦ Subtype.ext h
  obtain ⟨q₀, hq₀, hcomap⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hf₂ p hp
  let p' : PrimeSpectrum A := ⟨p, hp.isPrime⟩
  let q₀' : PrimeSpectrum S := ⟨q₀, hq₀⟩
  have hq₀' : PrimeSpectrum.comap f₂ q₀' = p' := PrimeSpectrum.ext hcomap
  have hqcomp : PrimeSpectrum.comap f₁ q' = PrimeSpectrum.comap φ q := by
    rw [← PrimeSpectrum.comap_comp_apply f₁ f₂ q, hcomp]
  have hpcomp : PrimeSpectrum.comap f₁ p' = PrimeSpectrum.comap φ q₀' := by
    rw [← hq₀', ← PrimeSpectrum.comap_comp_apply f₁ f₂ q₀', hcomp]
  have hspec : PrimeSpectrum.comap φ q₀' ⤳ PrimeSpectrum.comap φ q := by
    rw [← hpcomp, ← hqcomp]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp (Ideal.comap_mono hple)
  exact ⟨⟨p, hp⟩, hpcomp.trans (hE ⟨_, hf q₀'⟩ ⟨_, hf q⟩ hspec)⟩

/-- A morphism of affine schemes whose image lies in a specialization antichain of a Noetherian
target has finite image. -/
private lemma finite_range_of_affine_morphism
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T]
    [IsNoetherianRing Γ(T, ⊤)] (f : S ⟶ T) (E : Set T)
    (hE : ∀ x x' : E, x.1 ⤳ x'.1 → x.1 = x'.1)
    (hf : ∀ y : S, f y ∈ E) : (Set.range f.base).Finite := by
  let eS : S ≃ₜ PrimeSpectrum Γ(S, ⊤) := S.isoSpec.hom.homeomorph
  let eT : T ≃ₜ PrimeSpectrum Γ(T, ⊤) := T.isoSpec.hom.homeomorph
  let φ : Γ(T, ⊤) →+* Γ(S, ⊤) := f.appTop.hom
  let E' : Set (PrimeSpectrum Γ(T, ⊤)) := eT.symm ⁻¹' E
  have hE' : ∀ x x' : E', x.1 ⤳ x'.1 → x.1 = x'.1 := by
    intro x x' h
    simpa using congrArg eT
      (hE ⟨eT.symm x.1, x.2⟩ ⟨eT.symm x'.1, x'.2⟩ (h.map eT.symm.continuous))
  have hpoint (q : PrimeSpectrum Γ(S, ⊤)) :
      eT (f (eS.symm q)) = PrimeSpectrum.comap φ q := by
    have h := congrArg (fun k : S ⟶ Spec Γ(T, ⊤) => k (eS.symm q))
      (Scheme.isoSpec_hom_naturality f)
    have hsrc : S.isoSpec.hom (eS.symm q) = q := eS.apply_symm_apply q
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hsrc] at h
    exact h.symm
  have hf' : ∀ q : PrimeSpectrum Γ(S, ⊤), PrimeSpectrum.comap φ q ∈ E' := by
    intro q
    show eT.symm (PrimeSpectrum.comap φ q) ∈ E
    rw [← hpoint q]
    simpa using hf (eS.symm q)
  refine ((finite_range_comap_of_specializes_antichain φ E' hE' hf').image eT.symm).subset ?_
  rintro _ ⟨y, rfl⟩
  refine ⟨PrimeSpectrum.comap φ (eS y), ⟨eS y, rfl⟩, eT.injective ?_⟩
  simpa using (hpoint (eS y)).symm

/-- The morphism from the coproduct of the residue-field points of a set `E` is a
monomorphism. -/
private theorem mono_residueField_coproduct (X : Scheme.{u}) (E : Set X) :
    Mono (Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1)) := by
  let i := Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1)
  let e := sigmaMk (fun x : E ↦ Spec (.of (X.residueField x.1)) : E → Scheme)
  have hcomponent (x : E) :
      Sigma.ι (fun x : E ↦ Spec (.of (X.residueField x.1))) x ≫ i =
        X.fromSpecResidueField x.1 :=
    Sigma.ι_desc _ x
  have hbase (p : Σ x : E, Spec (.of (X.residueField x.1))) :
      i (e p) = p.1.1 := by
    rcases p with ⟨x, a⟩
    rw [sigmaMk_mk]
    show (Sigma.ι (fun x : E ↦ Spec (.of (X.residueField x.1))) x ≫ i) a = x.1
    rw [hcomponent]
    exact Scheme.fromSpecResidueField_apply _ _
  have hinj : Function.Injective i := by
    intro z z' h
    obtain ⟨⟨x, a⟩, rfl⟩ := e.surjective z
    obtain ⟨⟨y, b⟩, rfl⟩ := e.surjective z'
    obtain rfl : x = y := Subtype.ext ((hbase ⟨x, a⟩).symm.trans (h.trans (hbase ⟨y, b⟩)))
    rw [Subsingleton.elim a b]
  have : SurjectiveOnStalks i := by
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := @SurjectiveOnStalks)
      (sigmaOpenCover (fun x : E ↦ Spec (.of (X.residueField x.1))))]
    intro x
    show SurjectiveOnStalks
      (Sigma.ι (fun x : E ↦ Spec (.of (X.residueField x.1))) x ≫ i)
    rw [hcomponent x]
    infer_instance
  show Mono i
  exact SurjectiveOnStalks.mono_of_injective hinj

/-- Morphisms from the pieces of an open cover into a monomorphism `π` that agree with `f`
glue to a factorization of `f` through `π`. -/
private lemma exists_comp_eq_of_openCover_of_mono
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (π : Z ⟶ X) [Mono π] (𝒰 : Y.OpenCover)
    (k : ∀ i, 𝒰.X i ⟶ Z) (hk : ∀ i, k i ≫ π = 𝒰.f i ≫ f) :
    ∃ g : Y ⟶ Z, g ≫ π = f := by
  have hcompat (i j : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ k i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ k j := by
    apply (cancel_mono π).mp
    rw [Category.assoc, Category.assoc, hk, hk, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  exact ⟨𝒰.glueMorphisms k hcompat, 𝒰.hom_ext _ _ fun i ↦ by
    rw [← Category.assoc, 𝒰.ι_glueMorphisms k hcompat i, hk]⟩

/-- The factorization when the set of points is finite. -/
private lemma exists_factorization_of_finite_index
    {X Y : Scheme.{u}} (f : Y ⟶ X) (E : Set X) [IsReduced Y]
    (hEfin : E.Finite)
    (hE : ∀ x x' : E, x.1 ⤳ x'.1 → x.1 = x'.1)
    (hf : ∀ y : Y, f y ∈ E) :
    ∃ g : Y ⟶ ∐ fun x : E ↦ Spec (.of (X.residueField x.1)),
      g ≫ Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) = f := by
  have : T1Space E := t1Space_iff_specializes_imp_eq.mpr fun x y hxy ↦
    Subtype.ext (hE x y (hxy.map continuous_subtype_val))
  have : Finite E := Set.finite_coe_iff.mp hEfin
  let ff : Y → E := fun y ↦ ⟨f y, hf y⟩
  have hff : Continuous ff := (Scheme.Hom.continuous f).subtype_mk _
  let U : E → Y.Opens := fun x ↦ ⟨ff ⁻¹' {x}, hff.isOpen_preimage _ (isOpen_discrete {x})⟩
  have hU : IsOpenCover U := top_unique fun y _ ↦ Opens.mem_iSup.mpr ⟨ff y, by simp [U]⟩
  let 𝒰 := Y.openCoverOfIsOpenCover U hU
  have hpoint (x : E) (y : 𝒰.X x) : f (𝒰.f x y) = x.1 :=
    congrArg Subtype.val (show ff ((U x).ι y) = x from y.2)
  have hfactor (x : E) :
      ∃ q : 𝒰.X x ⟶ Spec (.of (X.residueField x.1)),
        q ≫ X.fromSpecResidueField x.1 = 𝒰.f x ≫ f := by
    have : IsOpenImmersion (𝒰.f x) := 𝒰.map_prop x
    have : IsReduced (𝒰.X x) := isReduced_of_isOpenImmersion (𝒰.f x)
    refine exists_comp_fromSpecResidueField_eq _ _ ?_
    rintro _ ⟨y, rfl⟩
    exact hpoint x y
  let gi (x : E) : 𝒰.X x ⟶ Spec (.of (X.residueField x.1)) :=
    Classical.choose (hfactor x)
  have hgi (x : E) : gi x ≫ X.fromSpecResidueField x.1 = 𝒰.f x ≫ f :=
    Classical.choose_spec (hfactor x)
  have : Mono (Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1)) :=
    mono_residueField_coproduct X E
  have hk (x : E) : (gi x ≫ Sigma.ι (fun x : E ↦ Spec (.of (X.residueField x.1))) x) ≫
      Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) = 𝒰.f x ≫ f := by
    rw [Category.assoc, Sigma.ι_desc, hgi]
  exact exists_comp_eq_of_openCover_of_mono f _ 𝒰 _ hk

/-- A factorization through the residue-field points of a subset extends to any larger set of
points. -/
private lemma factorization_include_finite_subset
    {X Y : Scheme.{u}} (F E : Set X) (hFE : F ⊆ E)
    (f : Y ⟶ X)
    (g : Y ⟶ ∐ fun x : F ↦ Spec (.of (X.residueField x.1)))
    (hg : g ≫ Sigma.desc (fun x : F ↦ X.fromSpecResidueField x.1) = f) :
    ∃ g' : Y ⟶ ∐ fun x : E ↦ Spec (.of (X.residueField x.1)),
      g' ≫ Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) = f := by
  let lift : (∐ fun x : F ↦ Spec (.of (X.residueField x.1))) ⟶
      ∐ fun x : E ↦ Spec (.of (X.residueField x.1)) :=
    Sigma.desc fun x : F ↦
      Sigma.ι (fun x : E ↦ Spec (.of (X.residueField x.1))) ⟨x.1, hFE x.2⟩
  have hlift : lift ≫ Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) =
      Sigma.desc (fun x : F ↦ X.fromSpecResidueField x.1) :=
    Sigma.hom_ext _ _ fun x ↦ by simp only [← Category.assoc, lift, Sigma.ι_desc]
  exact ⟨g ≫ lift, by rwa [Category.assoc, hlift]⟩

/-- **Stacks Project, Tag 0H1N.** A morphism from a reduced scheme into a locally Noetherian
scheme, whose image lies in a set having no nontrivial specializations among its points, factors
through the coproduct of the corresponding residue-field points. -/
@[stacks 0H1N]
theorem exists_factorization_through_residueFields
    {X Y : Scheme.{u}} (f : Y ⟶ X) (E : Set X)
    [IsLocallyNoetherian X] [IsReduced Y]
    (hE : ∀ x x' : E, x.1 ⤳ x'.1 → x.1 = x'.1)
    (hf : ∀ y : Y, f y ∈ E) :
    ∃ g : Y ⟶ ∐ fun x : E ↦ Spec (.of (X.residueField x.1)),
      g ≫ Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) = f := by
  let U (y : Y) : X.Opens := Classical.choose <|
    exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := ⊤) (by simp)
  have hUdata (y : Y) : IsAffineOpen (U y) ∧ f y ∈ U y ∧ (U y).carrier ⊆ Set.univ :=
    Classical.choose_spec <|
      exists_isAffineOpen_mem_and_subset (X := X) (x := f y) (U := ⊤) (by simp)
  let V (y : Y) : Y.Opens := Classical.choose <|
    exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := f ⁻¹ᵁ U y)
      (Set.mem_preimage.mpr (hUdata y).2.1)
  have hVdata (y : Y) : IsAffineOpen (V y) ∧ y ∈ V y ∧
      (V y).carrier ⊆ ↑(f ⁻¹ᵁ U y) :=
    Classical.choose_spec <|
      exists_isAffineOpen_mem_and_subset (X := Y) (x := y) (U := f ⁻¹ᵁ U y)
        (Set.mem_preimage.mpr (hUdata y).2.1)
  have hVU (y : Y) : V y ≤ f ⁻¹ᵁ U y := fun _ hz ↦ (hVdata y).2.2 hz
  have hcover : IsOpenCover V := top_unique fun y _ ↦ Opens.mem_iSup.mpr ⟨y, (hVdata y).2.1⟩
  let 𝒰 := Y.openCoverOfIsOpenCover V hcover
  let r (i : 𝒰.I₀) : 𝒰.X i ⟶ (U i).toScheme :=
    f.resLE (U i) (V i) (hVU i)
  let localMap (i : 𝒰.I₀) : 𝒰.X i ⟶ X := 𝒰.f i ≫ f
  have hcomp (i : 𝒰.I₀) : r i ≫ (U i).ι = localMap i :=
    Scheme.Hom.resLE_comp_ι (f := f) (U := U i) (V := V i) (e := hVU i)
  let EU (i : 𝒰.I₀) : Set (↑(U i)) := {z | (U i).ι z ∈ E}
  have hEU (i : 𝒰.I₀) :
      ∀ x x' : EU i, x.1 ⤳ x'.1 → x.1 = x'.1 := fun x x' hx ↦
    Subtype.ext (hE ⟨(U i).ι x.1, x.2⟩ ⟨(U i).ι x'.1, x'.2⟩ (hx.map (U i).ι.continuous))
  have hlocalRange (i : 𝒰.I₀) : (Set.range (localMap i).base).Finite := by
    have : IsAffine ((U i).toScheme) := (hUdata i).1
    have : IsAffine ((V i).toScheme) := (hVdata i).1
    have : IsAffine (𝒰.X i) := (hVdata i).1
    have : IsNoetherianRing Γ(X, U i) :=
      IsLocallyNoetherian.component_noetherian ⟨U i, (hUdata i).1⟩
    have : IsNoetherianRing Γ((U i).toScheme, ⊤) :=
      isNoetherianRing_of_ringEquiv _ <|
        (Scheme.Opens.topIso (U i)).symm.commRingCatIsoToRingEquiv
    have hz (z : 𝒰.X i) : (U i).ι (r i z) = f ((𝒰.f i) z) := by
      simpa only [Scheme.Hom.comp_apply, localMap] using
        congrArg (fun k : 𝒰.X i ⟶ X => k z) (hcomp i)
    have hlocal : ∀ z : 𝒰.X i, r i z ∈ EU i := by
      intro z
      show (U i).ι (r i z) ∈ E
      rw [hz]
      exact hf _
    have hrangeR : (Set.range (r i).base).Finite :=
      finite_range_of_affine_morphism (r i) (EU i) (hEU i) hlocal
    refine (hrangeR.image (U i).ι).subset ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨r i w, ⟨w, rfl⟩, by simpa only [localMap, Scheme.Hom.comp_apply] using hz w⟩
  let F (i : 𝒰.I₀) : Set X := Set.range (localMap i).base
  have hFfin (i : 𝒰.I₀) : (F i).Finite := hlocalRange i
  have hFsub (i : 𝒰.I₀) : F i ⊆ E := by
    rintro x ⟨y, rfl⟩
    exact hf ((𝒰.f i) y)
  have hFanti (i : 𝒰.I₀) :
      ∀ x x' : F i, x.1 ⤳ x'.1 → x.1 = x'.1 := fun x x' h ↦
    hE ⟨x.1, hFsub i x.2⟩ ⟨x'.1, hFsub i x'.2⟩ h
  have hfactor (i : 𝒰.I₀) :
      ∃ g : 𝒰.X i ⟶ ∐ fun x : E ↦ Spec (.of (X.residueField x.1)),
        g ≫ Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1) = localMap i := by
    have : IsReduced (𝒰.X i) := isReduced_of_isOpenImmersion (𝒰.f i)
    obtain ⟨g, hg⟩ := exists_factorization_of_finite_index (localMap i) (F i)
      (hFfin i) (hFanti i) (fun y ↦ ⟨y, rfl⟩)
    exact factorization_include_finite_subset (F i) E (hFsub i) (localMap i) g hg
  choose k hk using hfactor
  have : Mono (Sigma.desc (fun x : E ↦ X.fromSpecResidueField x.1)) :=
    mono_residueField_coproduct X E
  exact exists_comp_eq_of_openCover_of_mono f _ 𝒰 k hk

end AlgebraicGeometry
