module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcPlumbing
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.Immersion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.StalkIdealSheaf
public import StacksFrontier.RingTheory.Koszul.Descent
public import StacksFrontier.RingTheory.Regular.LocallySpanned
public import StacksCore.Tactic.StacksAttribute

/-!
# The regularity conditions on a quasi-compact immersion are fpqc local on the target

Let `i : Z ⟶ X` be a quasi-compact immersion of schemes. Stacks tag 0694 asserts that each of the
three conditions Koszul-regular, `H₁`-regular and quasi-regular of Stacks tag 063J is local on
the target for the fpqc topology. This file proves that, for all three conditions at once.

The quasi-compactness qualifier is not in the statement of Stacks tag 0694, and it is not forced
by the `AlgebraicGeometry.Scheme.Hom.ker` API on which the affine criteria of Stacks tags 063D and
063G rest: that API is applied to the canonical *closed* factor of the immersion, and a closed
immersion is affine, hence quasi-compact, whatever the immersion it factors. The qualifier is
consumed in exactly one place, descending the property of *being an immersion* along a surjective
flat quasi-compact morphism, which is Stacks tag 02L8
(`AlgebraicGeometry.isImmersion_inf_quasiCompact_descendsAlong`) and is known only for
quasi-compact immersions. It is in fact false without that qualifier, so the qualifier cannot be
dropped from the clauses below: the coproduct over the primes of the closed immersions
`Spec 𝔽ₚ ⟶ Spec ℤ` is not an immersion, while its base change along the fpqc covering
`Spec (∏ₚ ℤₚ) ⟶ Spec ℤ` is a regular immersion. The module docstring of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcOfImmersion` has the
details, and
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcCounterexample`
formalizes its two self-contained halves: that the range of the morphism is not locally closed,
so the morphism is not an immersion, and that `ℤ ⟶ ∏ₚ ℤₚ` is faithfully flat, so the covering is
an fpqc covering. For a morphism already known to be an immersion the argument of this
file therefore runs with no quasi-compactness at all; that is
`AlgebraicGeometry.immersionProperty_iff_of_fpqcZeroHypercover` in
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqcOfImmersion`, and the
fppf clauses of `StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFppf`
remove the qualifier outright by replacing Stacks tag 02L8 with its fppf form, Stacks tag 02YM;
the étale clauses of `StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.RegularImmersion` are the
special case of those for an étale covering. The fppf form is the strongest true reading of the
tag: it keeps the tag's quantification over an arbitrary morphism and shrinks only the topology,
and it cannot be enlarged back to fpqc.

## Main results

* `AlgebraicGeometry.isLocalAtTarget_koszulRegularImmersion_inf_quasiCompact_fpqc`,
  `AlgebraicGeometry.isLocalAtTarget_h1RegularImmersion_inf_quasiCompact_fpqc` and
  `AlgebraicGeometry.isLocalAtTarget_quasiRegularImmersion_inf_quasiCompact_fpqc`: **Stacks tag
  0694**, the Koszul-regular, `H₁`-regular and quasi-regular clauses. All three are stated as the
  infimum of the regularity property with `AlgebraicGeometry.QuasiCompact`.
* `AlgebraicGeometry.kerGeneratedBy_iff_isLocallySpannedBy`: over an affine scheme, the
  affine-open form of a regularity condition on the kernel of a quasi-compact morphism is the
  corresponding condition on the single ideal `ker Γ(X) → Γ(Z)`.

## Implementation notes

The criterion of Stacks tag 02KP that `Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` supplies
reduces fpqc locality to Zariski locality, stability under flat base change, and descent along
surjective flat quasi-compact morphisms. The three conditions enter only through a predicate on
finite families of elements of a commutative ring, so the whole argument is carried out once,
uniformly in that predicate and in the condition on immersions it induces; the three clauses are
then three instantiations. What the instantiation has to supply is
`AlgebraicGeometry.KerGeneratedBy`-form of the condition on immersions, which is parts (2), (3)
and (4) of Stacks tag 063G composed with the independence of the chosen open of Stacks tag 063J,
and the stability of the family predicate under flat ring maps; both are available for each of
the three conditions.

The uniform argument has three ingredients beyond what
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion` provides.

The first is the affine dictionary `kerGeneratedBy_iff_isLocallySpannedBy`: over an affine scheme
the affine-open condition on the kernel of a quasi-compact morphism is the condition of Stacks
tag 07CV on the single ideal `ker Γ(X) → Γ(Z)`. The zero locus of that ideal is the closure of
the image (`AlgebraicGeometry.Scheme.Hom.support_ker`), which matches the two ranges of
quantification; the passage between an arbitrary affine open and a principal localization is
`AlgebraicGeometry.exists_basicOpen_le_affine_inter` together with
`AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`, which computes the kernel on a smaller
affine open as the extension of the kernel on a larger one, and the generating family is carried
along by flatness of the restriction.

The second is the descent step, which the dictionary reduces to Stacks tag 068N: for a closed
immersion into an affine scheme and a faithfully flat morphism of affine schemes, the kernel of
the base change is the extension of the kernel (`Stacks.Flatness.ker_inl_of_isPushout` applied to
the cocartesian square of global sections of a cartesian square of affine schemes), so the
conclusion is exactly that the condition of Stacks tag 07CV descends along the faithfully flat
map of global sections.

The third is gluing, `kerGeneratedBy_of_forall_affine_pullback`: the affine-open condition is
local on the target by construction, so it follows from the condition on the base changes along
the inclusions of a family of affine opens covering the target, the kernels being compared by
`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion`.

Zariski locality is not reproved: it is
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_resLE` and
`Stacks.AlgebraicGeometry.RegularIdealSheaf.isKoszulRegularImmersion_of_resLE` with their two
companions, which is why the uniform statements take the two halves as hypotheses. Invariance
under an isomorphism of the ambient scheme, which those two halves do not give, comes for free:
an isomorphism is flat, so it is a case of flat base change.

## References

* [Stacks Project, Lemma 35.26.1 (Tag 0694)](https://stacks.math.columbia.edu/tag/0694)
* [Stacks Project, Lemma 34.2.6 (Tag 02KP)](https://stacks.math.columbia.edu/tag/02KP)
* [Stacks Project, Lemma 35.21.1 (Tag 02L8)](https://stacks.math.columbia.edu/tag/02L8)
* [Stacks Project, Definition 31.21.2 (Tag 063D)](https://stacks.math.columbia.edu/tag/063D)
* [Stacks Project, Lemma 31.20.3 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Definition 31.21.4 (Tag 063J)](https://stacks.math.columbia.edu/tag/063J)
* [Stacks Project, Lemma 31.21.4 (Tag 067P)](https://stacks.math.columbia.edu/tag/067P)
* [Stacks Project, Definition 10.69.1 (Tag 07CV)](https://stacks.math.columbia.edu/tag/07CV)
* [Stacks Project, Lemma 15.8.10 (Tag 068N)](https://stacks.math.columbia.edu/tag/068N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MorphismProperty Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

variable {Seq : ∀ {A : Type u} [CommRing A] {r : ℕ}, (Fin r → A) → Prop}

/-! ### Transport of the family predicate along a ring isomorphism -/

/-- A predicate on finite families that is stable under flat ring homomorphisms is transported by
a ring isomorphism, an isomorphism being flat. -/
theorem seq_of_ringEquiv
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) {r : ℕ} (f : Fin r → A)
    (hf : Seq f) : Seq fun i => e (f i) :=
  hSeq e.toRingHom (RingHom.Flat.of_bijective e.bijective) f hf

/-! ### The affine dictionary -/

/-- For a quasi-compact morphism into an affine scheme, a point in the closure of the image has
its prime ideal containing the kernel on global sections: the closure of the image is the support
of the kernel ideal sheaf, which over an affine open is the zero locus of the kernel there. -/
theorem ker_le_primeIdealOf_of_mem_closure_range {Z X : Scheme.{u}} (j : Z ⟶ X) [QuasiCompact j]
    [IsAffine X] (x : X) (hx : x ∈ closure (Set.range j.base)) :
    RingHom.ker (j.appTop).hom ≤
      ((isAffineOpen_top X).primeIdealOf ⟨x, trivial⟩).asIdeal := by
  have htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  have hxs : x ∈ j.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]; exact hx
  have h2 := (Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := j.ker) (U := ⟨⊤, htop⟩) (by trivial)).mp hxs
  rw [Scheme.Hom.ker_apply] at h2
  exact (mem_zeroLocus_iff_le_primeIdealOf htop _ ⟨x, trivial⟩).mp h2

/-- Over an affine scheme, the kernel of a quasi-compact morphism on a basic open is the extension
of its kernel on global sections. -/
private theorem ker_app_basicOpen {Z X : Scheme.{u}} (j : Z ⟶ X) [QuasiCompact j] [IsAffine X]
    (g : Γ(X, ⊤)) :
    RingHom.ker (j.app (X.basicOpen g)).hom
      = (RingHom.ker (j.appTop).hom).map
        (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op).hom := by
  have h1 := Scheme.IdealSheafData.map_ideal j.ker
    (U := ⟨X.basicOpen g, (isAffineOpen_top X).basicOpen g⟩) (V := ⟨⊤, isAffineOpen_top X⟩)
    (Subtype.coe_le_coe.mp le_top)
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at h1
  exact h1.symm

/-- **From the condition on one ideal to the affine-open condition.** Over an affine scheme, if
the kernel of a quasi-compact morphism `j` on global sections is locally spanned by a `Seq`-family
then the kernel of `j` on sections is generated by a `Seq`-family on an affine open around every
point of the closure of the image.

The witnessing affine open is the basic open of the element supplied by
`Ideal.IsLocallySpannedBy`, whose sections are a model of the principal localization there. -/
theorem kerGeneratedBy_of_isLocallySpannedBy
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z X : Scheme.{u}} (j : Z ⟶ X) [QuasiCompact j] [IsAffine X]
    (h : (RingHom.ker (j.appTop).hom).IsLocallySpannedBy Seq) :
    KerGeneratedBy Seq j := by
  have htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  intro x hx
  obtain ⟨g, hg, r, f, hseq, hspan⟩ := h _ (ker_le_primeIdealOf_of_mem_closure_range j x hx)
  have hV : IsAffineOpen (X.basicOpen g) := htop.basicOpen g
  have hxV : x ∈ X.basicOpen g :=
    (mem_basicOpen_iff_notMem_primeIdealOf htop g ⟨x, trivial⟩).mpr hg
  have _ := htop.isLocalization_basicOpen g
  let e : Localization.Away g ≃ₐ[Γ(X, ⊤)] Γ(X, X.basicOpen g) :=
    IsLocalization.algEquiv (Submonoid.powers g) _ _
  refine ⟨⟨X.basicOpen g, hV⟩, hxV, r, fun i => e (f i), ?_,
    seq_of_ringEquiv hSeq e.toRingEquiv f hseq⟩
  have halg : (X.presheaf.map (homOfLE (le_top : X.basicOpen g ≤ ⊤)).op).hom
      = e.toRingEquiv.toRingHom.comp (algebraMap Γ(X, ⊤) (Localization.Away g)) := by
    ext a
    exact (e.commutes a).symm
  rw [ker_app_basicOpen, halg, ← Ideal.map_map, hspan, Ideal.map_span, ← Set.range_comp]
  rfl

/-- **From the affine-open condition to the condition on one ideal.** The converse of
`AlgebraicGeometry.kerGeneratedBy_of_isLocallySpannedBy`.

A prime containing the kernel on global sections is the prime of a point of the closure of the
image, which the affine-open condition surrounds by an affine open `U` carrying a `Seq`-family
generating the kernel there. A basic open of the ambient affine scheme squeezed between the point
and `U` is simultaneously a principal localization of the global sections and of `Γ(X, U)`; the
family is carried into it by flatness of the second, and the kernel is computed there from the
kernel on `U` by `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal`. -/
theorem isLocallySpannedBy_of_kerGeneratedBy
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z X : Scheme.{u}} (j : Z ⟶ X) [QuasiCompact j] [IsAffine X]
    (h : KerGeneratedBy Seq j) :
    (RingHom.ker (j.appTop).hom).IsLocallySpannedBy Seq := by
  have htop : IsAffineOpen (⊤ : X.Opens) := isAffineOpen_top X
  intro p hp
  obtain ⟨y, hy⟩ := exists_primeIdealOf_eq_of_isAffineOpen htop p
  have hx : (y : X) ∈ closure (Set.range j.base) := by
    rw [← Scheme.Hom.support_ker, SetLike.mem_coe]
    refine (Scheme.IdealSheafData.mem_support_iff_of_mem
      (I := j.ker) (U := ⟨⊤, htop⟩) (by trivial)).mpr ?_
    rw [Scheme.Hom.ker_apply]
    exact (mem_zeroLocus_iff_le_primeIdealOf htop _ y).mpr (hy ▸ hp)
  obtain ⟨U, hxU, r, f, hker, hseq⟩ := h (y : X) hx
  obtain ⟨g₀, gU, he, hxg⟩ :=
    exists_basicOpen_le_affine_inter htop U.2 (y : X) ⟨by trivial, hxU⟩
  have hWU : X.basicOpen g₀ ≤ U.1 := he ▸ X.basicOpen_le gU
  have hWaff : IsAffineOpen (X.basicOpen g₀) := htop.basicOpen g₀
  let _ : Algebra Γ(X, U.1) Γ(X, X.basicOpen g₀) :=
    (X.presheaf.map (homOfLE hWU).op).hom.toAlgebra
  have _ : IsLocalization.Away gU Γ(X, X.basicOpen g₀) :=
    U.2.isLocalization_of_eq_basicOpen gU (homOfLE hWU) he
  have hflat : (X.presheaf.map (homOfLE hWU).op).hom.Flat :=
    IsLocalization.flat Γ(X, X.basicOpen g₀) (Submonoid.powers gU)
  have _ := htop.isLocalization_basicOpen g₀
  let e : Localization.Away g₀ ≃ₐ[Γ(X, ⊤)] Γ(X, X.basicOpen g₀) :=
    IsLocalization.algEquiv (Submonoid.powers g₀) _ _
  refine ⟨g₀, ?_, r, fun i => e.symm ((X.presheaf.map (homOfLE hWU).op).hom (f i)), ?_, ?_⟩
  · exact hy ▸ (mem_basicOpen_iff_notMem_primeIdealOf htop g₀ y).mp hxg
  · exact seq_of_ringEquiv hSeq e.symm.toRingEquiv _ (hSeq _ hflat f hseq)
  · have hkerW : RingHom.ker (j.app (X.basicOpen g₀)).hom
        = Ideal.span (Set.range fun i => (X.presheaf.map (homOfLE hWU).op).hom (f i)) := by
      have h1 := Scheme.IdealSheafData.map_ideal j.ker
        (U := ⟨X.basicOpen g₀, hWaff⟩) (V := U) hWU
      rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, hker, Ideal.map_span,
        ← Set.range_comp] at h1
      exact h1.symm
    have halg : (algebraMap Γ(X, ⊤) (Localization.Away g₀))
        = e.symm.toRingEquiv.toRingHom.comp
          (X.presheaf.map (homOfLE (le_top : X.basicOpen g₀ ≤ ⊤)).op).hom := by
      ext a
      exact (e.symm.commutes a).symm
    rw [halg, ← Ideal.map_map, ← ker_app_basicOpen, hkerW, Ideal.map_span, ← Set.range_comp]
    rfl

/-- **The affine dictionary.** Over an affine scheme, the affine-open form of a regularity
condition on the kernel of a quasi-compact morphism is the corresponding condition of Stacks tag
07CV on the single ideal `ker Γ(X) → Γ(Z)`. -/
theorem kerGeneratedBy_iff_isLocallySpannedBy
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z X : Scheme.{u}} (j : Z ⟶ X) [QuasiCompact j] [IsAffine X] :
    KerGeneratedBy Seq j ↔ (RingHom.ker (j.appTop).hom).IsLocallySpannedBy Seq :=
  ⟨isLocallySpannedBy_of_kerGeneratedBy hSeq j, kerGeneratedBy_of_isLocallySpannedBy hSeq j⟩

/-! ### Descent of the affine-open condition along a faithfully flat covering -/

/-- **The descent step.** Let `j : Z ⟶ X` be a closed immersion of affine schemes and let
`g : Y ⟶ X` be a surjective flat morphism of affine schemes. If the base change of `j` along `g`
satisfies the affine-open condition, so does `j`, provided the corresponding condition on ideals
descends along faithfully flat ring maps.

The affine dictionary turns both sides into the condition on a single ideal, and the kernel of
the base change on global sections is the extension of the kernel of `j`, because the cartesian
square of affine schemes gives a cocartesian square of global sections one leg of which is
surjective. -/
theorem kerGeneratedBy_of_faithfullyFlat_cover
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    {Z X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (j : Z ⟶ X) (g : Y ⟶ X)
    [IsClosedImmersion j] [Flat g] [Surjective g]
    (h : KerGeneratedBy Seq (pullback.snd j g)) : KerGeneratedBy Seq j := by
  have _ : IsAffine Z := isAffine_of_isAffineHom j
  refine kerGeneratedBy_of_isLocallySpannedBy hSeq j (hdesc (g.appTop).hom
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
      ⟨inferInstance, inferInstance⟩) _ ?_)
  have hker : RingHom.ker ((pullback.snd j g).appTop).hom
      = Ideal.map (g.appTop).hom (RingHom.ker (j.appTop).hom) :=
    Stacks.Flatness.ker_inl_of_isPushout
      (isPushout_appTop_of_isPullback (IsPullback.of_hasPullback j g).flip)
      (j.app_surjective ⊤ (isAffineOpen_top X))
  rw [← hker]
  exact isLocallySpannedBy_of_kerGeneratedBy hSeq (pullback.snd j g) h

/-! ### The affine-open condition is local on the target -/

/-- A `Seq`-family generating the kernel of `f'` on an affine open `W` of `V` is carried by the
comparison isomorphism to a `Seq`-family generating the kernel of `f` on `iV ''ᵁ W`, for `f'` the
base change of `f` along an open immersion `iV`. -/
private theorem exists_seq_ker_of_isPullback_of_isOpenImmersion
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {X Y U V : Scheme.{u}} (f : X ⟶ Y) (f' : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [QuasiCompact f] (H : IsPullback f' iU iV f) (W : V.affineOpens)
    {r : ℕ} {g : Fin r → Γ(V, W.1)} (hker : RingHom.ker (f'.app W.1).hom = Ideal.span (Set.range g))
    (hseq : Seq g) :
    ∃ (r : ℕ) (g' : Fin r → Γ(Y, iV ''ᵁ W.1)),
      RingHom.ker (f.app (iV ''ᵁ W.1)).hom = Ideal.span (Set.range g') ∧ Seq g' := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback H.flip inferInstance
  let e := (iV.appIso W.1).symm.commRingCatIsoToRingEquiv
  refine ⟨r, fun a => e (g a), ?_, seq_of_ringEquiv hSeq e g hseq⟩
  have hk := Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f f' iU iV H W
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply, hker,
    show ((iV.appIso W.1).inv).hom = e.toRingHom from rfl] at hk
  have hh := congrArg (Ideal.map e.toRingHom) hk.symm
  rwa [Ideal.map_span, ← Set.range_comp,
    Ideal.map_comap_of_surjective e.toRingHom e.surjective] at hh

/-- **Gluing the affine-open condition.** The affine-open condition on the kernel of a closed
immersion holds as soon as it holds for the base change along the inclusion of some affine open
around every point of the target: the witnessing affine opens upstairs are affine opens of the
target, and the two kernels on their sections correspond under the comparison isomorphism of the
open immersion. -/
theorem kerGeneratedBy_of_forall_affine_pullback
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z X : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    (h : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ KerGeneratedBy Seq (pullback.snd j U.1.ι)) :
    KerGeneratedBy Seq j := by
  intro x hx
  rw [j.isClosedEmbedding.isClosed_range.closure_eq] at hx
  obtain ⟨U, hxU, hU⟩ := h x
  have _ : IsAffine U.1.toScheme := U.2
  have hx' : (⟨x, hxU⟩ : U.1) ∈ closure (Set.range (pullback.snd j U.1.ι).base) :=
    subset_closure (by rw [Scheme.Pullback.range_snd]; exact hx)
  obtain ⟨V, hxV, r, f, hker, hseq⟩ := hU ⟨x, hxU⟩ hx'
  obtain ⟨r', g, hg, hs⟩ := exists_seq_ker_of_isPullback_of_isOpenImmersion hSeq j
    (pullback.snd j U.1.ι) (pullback.fst j U.1.ι) U.1.ι (IsPullback.of_hasPullback j U.1.ι).flip
    V hker hseq
  exact ⟨⟨U.1.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.1.ι⟩, ⟨⟨x, hxU⟩, hxV, rfl⟩, r', g, hg, hs⟩

/-! ### The morphism property attached to a condition on immersions -/

/-- The morphism property of being an immersion that satisfies `Pred`. -/
def immersionProperty (Pred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Prop) :
    MorphismProperty Scheme.{u} :=
  fun _ _ f => ∃ hf : IsImmersion f, @Pred _ _ f hf

variable {Pred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i], Prop}

/-- A condition on immersions is transported along an equality of morphisms: the two immersion
hypotheses are propositions, hence equal. -/
private theorem pred_congr {Z X : Scheme.{u}} {i i' : Z ⟶ X} [IsImmersion i] [IsImmersion i']
    (h : i = i') (hi : Pred i) : Pred i' := by
  subst h
  exact hi

/-- **Flat base change.** If a condition on immersions is read off the kernel of a closed factor
through any open in which the immersion is closed, then it is stable under base change along a
flat morphism: the base change of the canonical closed factor of `i` is a closed immersion into
the preimage of the canonical open, and flat base change for the affine-open condition is
`AlgebraicGeometry.kerGeneratedBy_of_isPullback`.

This is the immersion-level form of the relevant parts of Stacks tag 067P. -/
theorem pred_of_isPullback_of_flat
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} [IsImmersion i] {j : Z' ⟶ X'} [IsImmersion j]
    {k : Z' ⟶ Z} {g : X' ⟶ X} [Flat g] (H : IsPullback j k g i) (h : Pred i) : Pred j := by
  have hjD : ∀ z, j.base z ∈ g ⁻¹ᵁ i.coborderRange := by
    intro z
    show g.base (j.base z) ∈ i.coborderRange
    rw [← Scheme.Hom.comp_apply, H.w]
    exact subset_coborder ⟨k.base z, rfl⟩
  let l : Z' ⟶ (g ⁻¹ᵁ i.coborderRange).toScheme :=
    IsOpenImmersion.lift (g ⁻¹ᵁ i.coborderRange).ι j (by
      rintro _ ⟨z, rfl⟩
      exact ⟨⟨j.base z, hjD z⟩, rfl⟩)
  have hlD : l ≫ (g ⁻¹ᵁ i.coborderRange).ι = j := IsOpenImmersion.lift_fac _ _ _
  have hcomm : k ≫ i.liftCoborder = l ≫ g ∣_ i.coborderRange := by
    apply (cancel_mono i.coborderRange.ι).mp
    rw [Category.assoc, i.liftCoborder_ι, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, hlD]
    exact H.w.symm
  have houter : IsPullback k (l ≫ (g ⁻¹ᵁ i.coborderRange).ι)
      (i.liftCoborder ≫ i.coborderRange.ι) g := by
    rw [hlD, i.liftCoborder_ι]
    exact H.flip
  have hsq := (houter.of_bot hcomm (isPullback_morphismRestrict g i.coborderRange)).flip
  have _ : IsClosedImmersion l := MorphismProperty.of_isPullback hsq.flip inferInstance
  have _ : Flat (g ∣_ i.coborderRange) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (isPullback_morphismRestrict g i.coborderRange).flip inferInstance
  rw [hPred j (g ⁻¹ᵁ i.coborderRange) l hlD]
  exact kerGeneratedBy_of_isPullback hSeq hsq.flip
    ((hPred i i.coborderRange i.liftCoborder i.liftCoborder_ι).mp h)

/-- The morphism property of being an immersion satisfying a condition read off the kernel of a
closed factor respects isomorphisms. Precomposition with an isomorphism changes neither the
closure of the image nor the kernel on sections; postcomposition is flat base change, an
isomorphism being flat. -/
theorem immersionProperty_respectsIso
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV)) :
    (immersionProperty Pred).RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · rintro X Y Z e f ⟨hi, hf⟩
    have _ := hi
    have _ : IsImmersion (e.hom ≫ f) := inferInstance
    exact ⟨inferInstance, (hPred (e.hom ≫ f) f.coborderRange (e.hom ≫ f.liftCoborder)
        (by rw [Category.assoc, f.liftCoborder_ι])).mpr
      (kerGeneratedBy_iso_comp e f.liftCoborder
        ((hPred f f.coborderRange f.liftCoborder f.liftCoborder_ι).mp hf))⟩
  · rintro X Y Z e f ⟨hi, hf⟩
    have _ := hi
    have _ : IsImmersion (f ≫ e.hom) := inferInstance
    exact ⟨inferInstance, pred_of_isPullback_of_flat hSeq hPred
      (IsPullback.of_horiz_isIso
        (show CommSq (𝟙 X) (f ≫ e.hom) f e.inv from ⟨by simp⟩)).flip hf⟩

/-- Being an immersion satisfying a condition read off the kernel of a closed factor is stable
under flat base change. -/
theorem immersionProperty_isStableUnderFlatBaseChange
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV)) :
    Stacks.Descent.IsStableUnderFlatBaseChange (immersionProperty Pred) where
  isStableUnderBaseChangeAlong q := by
    refine ⟨fun {_ _ _ _ g} pb ⟨hi, hg⟩ ↦ ?_⟩
    have _ := hi
    have _ : IsImmersion g := hi
    have _ : IsImmersion _ := MorphismProperty.of_isPullback pb hi
    refine ⟨inferInstance, ?_⟩
    exact pred_of_isPullback_of_flat hSeq hPred pb.flip hg

/-! ### Zariski locality -/

/-- **Zariski locality.** The morphism property of being an immersion satisfying a condition read
off the kernel of a closed factor is Zariski local on the target as soon as the condition glues
along an open cover of the target. Restriction to an open is a case of flat base change, so only
the gluing half has to be supplied. -/
theorem immersionProperty_isZariskiLocalAtTarget
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i) :
    IsZariskiLocalAtTarget (immersionProperty Pred) := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  apply IsZariskiLocalAtTarget.mk'
  · rintro X Y f U ⟨hi, hf⟩
    have _ := hi
    refine ⟨inferInstance, ?_⟩
    exact pred_of_isPullback_of_flat hSeq hPred (isPullback_morphismRestrict f U) hf
  · rintro X Y f ι U hU hf
    have hfImm : IsImmersion f :=
      IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsImmersion) U hU fun a => (hf a).1
    have _ := hfImm
    refine ⟨hfImm, hglue f U hU fun k => ?_⟩
    exact pred_congr (Scheme.Hom.resLE_eq_morphismRestrict (f := f) (U := U k)).symm (hf k).2

/-! ### Invariance of the affine-open condition under an isomorphism of the target -/

/-- **The affine-open condition is invariant under an isomorphism of the target.** Postcomposing
with an isomorphism carries affine opens to affine opens and identifies the kernels on their
sections, by `AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` applied to the
square exhibiting `j` as the base change of `j ≫ ε.hom` along `ε.hom`. -/
theorem kerGeneratedBy_comp_iso
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z W X : Scheme.{u}} (j : Z ⟶ W) [QuasiCompact j] (ε : W ≅ X)
    (h : KerGeneratedBy Seq j) : KerGeneratedBy Seq (j ≫ ε.hom) := by
  have hsq : IsPullback j (𝟙 Z) ε.hom (j ≫ ε.hom) :=
    (IsPullback.of_horiz_isIso (show CommSq (𝟙 Z) j (j ≫ ε.hom) ε.hom from ⟨by simp⟩)).flip
  intro x hx
  obtain ⟨y, rfl⟩ := (ConcreteCategory.bijective_of_isIso ε.hom.base).2 x
  have hpre : ε.hom.base ⁻¹' Set.range (j ≫ ε.hom).base = Set.range j.base := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.preimage_image_eq _ (ConcreteCategory.bijective_of_isIso ε.hom.base).1]
  have hopen := (ε.hom.isOpenEmbedding).isOpenMap.preimage_closure_eq_closure_preimage
    ε.hom.base.hom.continuous (Set.range (j ≫ ε.hom).base)
  rw [hpre] at hopen
  have hy : y ∈ closure (Set.range j.base) := by rw [← hopen]; exact hx
  obtain ⟨U, hyU, r, f, hker, hseq⟩ := h y hy
  obtain ⟨r', g, hg, hs⟩ := exists_seq_ker_of_isPullback_of_isOpenImmersion hSeq (j ≫ ε.hom) j
    (𝟙 Z) ε.hom hsq U hker hseq
  exact ⟨⟨ε.hom ''ᵁ U.1, U.2.image_of_isOpenImmersion ε.hom⟩, ⟨y, hyU, rfl⟩, r', g, hg, hs⟩

/-- The affine-open condition is unchanged by an isomorphism of the target. -/
theorem kerGeneratedBy_comp_iso_iff
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    {Z W X : Scheme.{u}} (j : Z ⟶ W) [QuasiCompact j] (ε : W ≅ X) :
    KerGeneratedBy Seq (j ≫ ε.hom) ↔ KerGeneratedBy Seq j := by
  refine ⟨fun h => ?_, kerGeneratedBy_comp_iso hSeq j ε⟩
  have h2 := kerGeneratedBy_comp_iso hSeq (j ≫ ε.hom) ε.symm h
  rwa [Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id] at h2

/-- **The condition on a closed immersion is read off its own kernel.** For a closed immersion
the ambient scheme is itself an open in which the immersion is closed, up to the isomorphism
`(⊤ : X.Opens).toScheme ≅ X`. -/
theorem pred_iff_kerGeneratedBy_of_isClosedImmersion
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :
    Pred i ↔ KerGeneratedBy Seq i := by
  have hij : (i ≫ X.topIso.inv) ≫ (⊤ : X.Opens).ι = i := by simp
  rw [hPred i (⊤ : X.Opens) (i ≫ X.topIso.inv) hij,
    ← kerGeneratedBy_comp_iso_iff hSeq (i ≫ X.topIso.inv) X.topIso,
    Scheme.topIso_hom, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]

/-! ### Descent along a surjective flat quasi-compact morphism -/

/-- A property respecting isomorphisms holds for `pullback.snd f g` as soon as it holds for the
second leg of some cartesian square over `f` and `g`. -/
public theorem pullbackSnd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {A X V Y : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
    (hp : IsPullback a b f g) (h : P b) : P (pullback.snd f g) := by
  have he := MorphismProperty.RespectsIso.precomp P hp.isoPullback.inv _ h
  simpa only [hp.isoPullback_inv_snd] using he

/-- The converse reading of the previous lemma. -/
public theorem of_pullbackSnd_of_isPullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {A X V Y : Scheme.{u}} {a : A ⟶ X} {b : A ⟶ V} {f : X ⟶ Y} {g : V ⟶ Y}
    (hp : IsPullback a b f g) (h : P (pullback.snd f g)) : P b := by
  have he := MorphismProperty.RespectsIso.precomp P hp.isoPullback.hom _ h
  simpa only [hp.isoPullback_hom_snd] using he

/-- Pulling back along a morphism that factors through a flat morphism: if the base change of `f`
along `g` has `P`, so does its base change along `q ≫ g` for `q` flat. -/
public theorem pullbackSnd_of_factor (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [Stacks.Descent.IsStableUnderFlatBaseChange P]
    {X Y V W : Scheme.{u}} (f : X ⟶ Y) (g : V ⟶ Y) (q : W ⟶ V) [Flat q]
    (hf : P (pullback.snd f g)) : P (pullback.snd f (q ≫ g)) := by
  have hq := (Stacks.Descent.IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong
    (P := P) q).of_isPullback (IsPullback.of_hasPullback (pullback.snd f g) q) hf
  have he := MorphismProperty.RespectsIso.precomp P (pullbackLeftPullbackSndIso f g q).inv _ hq
  simpa only [pullbackLeftPullbackSndIso_inv_snd_snd] using he

/-- Intersecting with quasi-compactness preserves stability under flat base change. -/
private theorem isStableUnderFlatBaseChange_inf_quasiCompact (P : MorphismProperty Scheme.{u})
    [Stacks.Descent.IsStableUnderFlatBaseChange P] :
    Stacks.Descent.IsStableUnderFlatBaseChange (P ⊓ @QuasiCompact) := by
  refine ⟨fun q => ⟨fun {_ _ _ _ g} pb hg ↦ ⟨?_, ?_⟩⟩⟩
  · exact (Stacks.Descent.IsStableUnderFlatBaseChange.isStableUnderBaseChangeAlong
      (P := P) q).of_isPullback pb hg.1
  · exact quasiCompact_isStableUnderBaseChange.of_isPullback pb hg.2

/-- Intersecting with quasi-compactness preserves Zariski locality on the target. -/
private theorem isZariskiLocalAtTarget_inf_quasiCompact (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] : IsZariskiLocalAtTarget (P ⊓ @QuasiCompact) := by
  have _ : IsZariskiLocalAtTarget (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc.of_le
      Scheme.zariskiPrecoverage_le_fpqcPrecoverage
  exact MorphismProperty.IsLocalAtTarget.inf _ _

/-- **The descent step over an affine base, with an affine covering scheme.** The canonical closed
factor of `f` is covered by affine opens, and over each the covering morphism restricts to a
surjective flat morphism of affine schemes, so the affine descent step applies. -/
theorem immersionProperty_inf_quasiCompact_of_pullbackSnd_of_isAffine
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    [(immersionProperty Pred).RespectsIso]
    [Stacks.Descent.IsStableUnderFlatBaseChange (immersionProperty Pred)]
    {S X Y : Scheme.{u}} [IsAffine S] [IsAffine X] (c : X ⟶ S) (f : Y ⟶ S)
    [Surjective c] [Flat c]
    (hf : (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.snd f c)) :
    (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f := by
  have hImm : (@IsImmersion ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f :=
    MorphismProperty.of_pullback_snd_of_descendsAlong
      (Q := (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}))
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ ⟨hf.1.1, hf.2⟩
  have _ := hImm.1
  refine ⟨⟨hImm.1, (hPred f f.coborderRange f.liftCoborder f.liftCoborder_ι).mpr ?_⟩, hImm.2⟩
  refine kerGeneratedBy_of_forall_affine_pullback hSeq f.liftCoborder fun x => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    f.coborderRange.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ x) isOpen_univ
  change f.coborderRange.toScheme.Opens at U
  have _ : IsAffine U.toScheme := hU
  refine ⟨⟨U, hU⟩, hxU, ?_⟩
  have hc2 : IsPullback (𝟙 Y) f.liftCoborder f f.coborderRange.ι :=
    IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  have hvsq := (IsPullback.of_hasPullback f.liftCoborder U.ι).paste_horiz hc2
  have _ : IsAffine (pullback c (U.ι ≫ f.coborderRange.ι)) := inferInstance
  have hbase : immersionProperty Pred
      (pullback.snd f (pullback.snd c (U.ι ≫ f.coborderRange.ι) ≫
        (U.ι ≫ f.coborderRange.ι))) := by
    rw [← pullback.condition]
    exact pullbackSnd_of_factor _ f c (pullback.fst c (U.ι ≫ f.coborderRange.ι)) hf.1
  obtain ⟨_, hireg⟩ := of_pullbackSnd_of_isPullback (immersionProperty Pred)
    ((IsPullback.of_hasPullback (pullback.snd f.liftCoborder U.ι)
      (pullback.snd c (U.ι ≫ f.coborderRange.ι))).paste_horiz hvsq) hbase
  exact kerGeneratedBy_of_faithfullyFlat_cover hSeq hdesc (pullback.snd f.liftCoborder U.ι)
    (pullback.snd c (U.ι ≫ f.coborderRange.ι))
    ((pred_iff_kerGeneratedBy_of_isClosedImmersion hSeq hPred _).mp hireg)

/-- **The descent step over an affine base.** The covering scheme may be taken affine: it is
quasi-compact, so some affine scheme maps onto it by a surjective local isomorphism, and
precomposing the covering morphism with that keeps it surjective and flat while the hypothesis is
carried along by flat base change. -/
theorem immersionProperty_inf_quasiCompact_of_pullbackFst
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    [(immersionProperty Pred).RespectsIso]
    [Stacks.Descent.IsStableUnderFlatBaseChange (immersionProperty Pred)]
    {R : CommRingCat.{u}} {X Y : Scheme.{u}} (c : X ⟶ Spec R) (f : Y ⟶ Spec R)
    (hc : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) c)
    (hf : (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst c f)) :
    (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) f := by
  have _ := Stacks.Descent.flat_isZariskiLocalAtSource.{u}
  have _ := Flat.instIsMultiplicativeScheme.{u}.toContainsIdentities
  have _ := IsLocalIso.instIsMultiplicativeScheme.{u}.toContainsIdentities
  obtain ⟨⟨hsurj, hflat⟩, hqc⟩ := hc
  have _ : Surjective c := hsurj
  have _ : Flat c := hflat
  have _ : QuasiCompact c := hqc
  have _ : CompactSpace X := (quasiCompact_iff_compactSpace c).mp hqc
  obtain ⟨T, p, hps, hpl, hTa⟩ := X.exists_hom_isAffine_of_isZariskiLocalAtSource @IsLocalIso
  have _ := hTa
  have _ : Surjective p := hps
  have _ : Flat p := IsLocalIso.le_of_isZariskiLocalAtSource @Flat _ _ p hpl
  have _ : MorphismProperty.RespectsIso (@QuasiCompact : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@QuasiCompact : MorphismProperty Scheme.{u}))
  have _ : (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u}).RespectsIso :=
    MorphismProperty.RespectsIso.inf _ _
  have _ := isStableUnderFlatBaseChange_inf_quasiCompact (immersionProperty Pred)
  refine immersionProperty_inf_quasiCompact_of_pullbackSnd_of_isAffine hSeq hdesc hPred
    (p ≫ c) f (pullbackSnd_of_factor _ f c p
      (pullbackSnd_of_isPullback _ (IsPullback.of_hasPullback c f).flip hf))

/-- **Descent along a surjective flat quasi-compact morphism.** Hypothesis (3) of Stacks tag
02KP for the morphism property of being a quasi-compact immersion satisfying a condition read off
the kernel of a closed factor. -/
theorem immersionProperty_inf_quasiCompact_descendsAlong
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i) :
    MorphismProperty.DescendsAlong
      (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isStableUnderFlatBaseChange hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  have _ := isZariskiLocalAtTarget_inf_quasiCompact (immersionProperty Pred)
  have _ := Stacks.Descent.isStableUnderBaseChange_surjective_inf_flat_inf_quasiCompact.{u}
  exact IsZariskiLocalAtTarget.descendsAlong
    (immersionProperty Pred ⊓ @QuasiCompact) (@Surjective ⊓ @Flat ⊓ @QuasiCompact)
    fun {_ _ _} c f hc hfst =>
      immersionProperty_inf_quasiCompact_of_pullbackFst hSeq hdesc hPred c f hc hfst

/-- **The uniform form of Stacks tag 0694.** A condition on immersions that is read off the kernel
of a closed factor through any open in which the immersion is closed, whose family predicate is
stable under flat ring maps and whose ideal-theoretic form descends along faithfully flat ring
maps, and which glues along open covers of the target, is fpqc local on the target when combined
with quasi-compactness. -/
theorem isLocalAtTarget_immersionProperty_inf_quasiCompact_fpqc
    (hSeq : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.Flat →
      ∀ {r : ℕ} (f : Fin r → A), Seq f → Seq fun i => φ (f i))
    (hdesc : ∀ {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B), φ.FaithfullyFlat →
      ∀ I : Ideal A, (I.map φ).IsLocallySpannedBy Seq → I.IsLocallySpannedBy Seq)
    (hPred : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (V : X.Opens)
      (jV : Z ⟶ V.toScheme) [IsClosedImmersion jV], jV ≫ V.ι = i →
        (Pred i ↔ KerGeneratedBy Seq jV))
    (hglue : ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] {ι : Type u} (V : ι → X.Opens),
      iSup V = ⊤ → (∀ k, Pred (i.resLE (V k) (i ⁻¹ᵁ V k) le_rfl)) → Pred i) :
    MorphismProperty.IsLocalAtTarget
      (immersionProperty Pred ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := by
  have _ := immersionProperty_respectsIso hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isStableUnderFlatBaseChange hSeq hPred (Pred := Pred)
  have _ := immersionProperty_isZariskiLocalAtTarget hSeq hPred hglue (Pred := Pred)
  have _ := isZariskiLocalAtTarget_inf_quasiCompact (immersionProperty Pred)
  have _ := isStableUnderFlatBaseChange_inf_quasiCompact (immersionProperty Pred)
  have _ := immersionProperty_inf_quasiCompact_descendsAlong hSeq hdesc hPred hglue (Pred := Pred)
  exact Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-! ### The three clauses of Stacks tag 0694 -/

/-- **Stacks Project, Tag 0694, the Koszul-regular clause.** Being a quasi-compact Koszul-regular
immersion of schemes is local on the target for the fpqc topology. -/
@[stacks 0694 "koszul_regular", sga "6 VII 1.5" "special case"]
theorem isLocalAtTarget_koszulRegularImmersion_inf_quasiCompact_fpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f => ∃ hf : IsImmersion f, @IsKoszulRegularImmersion _ _ f hf) ⊓
        (@QuasiCompact : MorphismProperty Scheme.{u})) Scheme.fpqcPrecoverage :=
  isLocalAtTarget_immersionProperty_inf_quasiCompact_fpqc
    (Seq := fun f => Koszul.IsKoszulRegular f)
    (Pred := fun i => IsKoszulRegularImmersion i)
    isKoszulRegular_of_ringHomFlat
    (by intro A B _ _ φ hφ I h; exact (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).1 h)
    (by
      intro Z X i _ V jV _ hij
      exact (isKoszulRegularImmersion_iff_of_open i V jV hij).trans
        (isKoszulRegularIdealSheaf_iff_kerGeneratedBy jV))
    isKoszulRegularImmersion_of_resLE

/-- **Stacks Project, Tag 0694, the `H₁`-regular clause.** Being a quasi-compact `H₁`-regular
immersion of schemes is local on the target for the fpqc topology. -/
@[stacks 0694 "h1_regular"]
theorem isLocalAtTarget_h1RegularImmersion_inf_quasiCompact_fpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f => ∃ hf : IsImmersion f, @IsH1RegularImmersion _ _ f hf) ⊓
        (@QuasiCompact : MorphismProperty Scheme.{u})) Scheme.fpqcPrecoverage :=
  isLocalAtTarget_immersionProperty_inf_quasiCompact_fpqc
    (Seq := fun f => Koszul.IsH1Regular f)
    (Pred := fun i => IsH1RegularImmersion i)
    isH1Regular_of_ringHomFlat
    (by intro A B _ _ φ hφ I h; exact (Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.1 h)
    (by
      intro Z X i _ V jV _ hij
      exact (isH1RegularImmersion_iff_of_open i V jV hij).trans
        (isH1RegularIdealSheaf_iff_kerGeneratedBy jV))
    isH1RegularImmersion_of_resLE

/-- **Stacks Project, Tag 0694, the quasi-regular clause.** Being a quasi-compact quasi-regular
immersion of schemes is local on the target for the fpqc topology. -/
@[stacks 0694 "quasi_regular", ega "IV 19.1.5" "(ii), special case"]
theorem isLocalAtTarget_quasiRegularImmersion_inf_quasiCompact_fpqc :
    MorphismProperty.IsLocalAtTarget
      ((fun _ _ f => ∃ hf : IsImmersion f,
          @RegularIdealSheaf.IsQuasiRegularImmersion _ _ f hf) ⊓
        (@QuasiCompact : MorphismProperty Scheme.{u})) Scheme.fpqcPrecoverage :=
  isLocalAtTarget_immersionProperty_inf_quasiCompact_fpqc
    (Seq := fun {A} _ _ f => RingTheory.Sequence.IsQuasiRegular A (List.ofFn f))
    (Pred := fun i => RegularIdealSheaf.IsQuasiRegularImmersion i)
    isQuasiRegular_of_ringHomFlat
    (by
      intro A B _ _ φ hφ I h
      exact (Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy I).mp
        ((Koszul.regular_ideals_of_faithfullyFlat φ hφ I).2.2
          ((Ideal.isQuasiregularIdeal_iff_isLocallySpannedBy (I.map φ)).mpr h)))
    (by
      intro Z X i _ V jV _ hij
      exact (RegularIdealSheaf.isQuasiRegularImmersion_iff_of_open i V jV hij).trans
        (isQuasiRegularIdealSheaf_iff_kerGeneratedBy jV))
    RegularIdealSheaf.isQuasiRegularImmersion_of_resLE

end AlgebraicGeometry

end
