module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Perfect.Limits
public import StacksCore.Tactic.StacksAttribute

/-!
# Images of the stages of an inverse system in a constructible set

In the descent situation for a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms, a locally constructible subset of one stage which
contains the image of the limit also contains the image of every sufficiently large stage.
The key step is that an empty fibre product over the limit is already empty over every
sufficiently large stage.

"For all sufficiently large indices" is expressed by the `Filter.atTop` filter. Since a
transition morphism to the fixed stage needs a proof that the index is later than the fixed
index, that proof is quantified inside the eventual assertion; its value is immaterial because
inequalities in a preorder are propositions.

## Main results

* `AlgebraicGeometry.eventually_isEmpty_pullback`: eventual emptiness of the finite-stage fibre
  products.
* `AlgebraicGeometry.eventually_range_transition_subset_of_isLocallyConstructible`: eventual
  containment of the images of the transition morphisms in a locally constructible set.

## Implementation notes

The constructible statement is checked on a finite cover of the fixed stage by affine opens. On
an affine open the complement of the given set is constructible, hence the image of a morphism
from a quasi-compact scheme (`PrimeSpectrum.exists_range_eq_of_isConstructible`), and the
emptiness statement applies to that morphism.

## References

* [Stacks Project, Tag 05F3](https://stacks.math.columbia.edu/tag/05F3)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Filter Opposite

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05F3.** If the base change of a quasi-compact scheme to the limit of a
directed inverse system is empty, then its base change to every sufficiently late stage is
empty. -/
@[stacks 05F3, ega "IV 8.3.6" "Nontrivial direction"]
lemma eventually_isEmpty_pullback
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation.{u, u} I)
    (T : Scheme.{u}) [CompactSpace T]
    (t : T ⟶ D.system.obj (Opposite.op D.base))
    (hT : IsEmpty
      (pullback t (D.limitCone.π.app (Opposite.op D.base)) : Scheme)) :
    ∀ᶠ i in Filter.atTop, ∀ h : D.base ≤ i,
      IsEmpty (pullback t (D.system.map (homOfLE h).op) : Scheme) := by
  classical
  by_contra! H
  have : MorphismProperty.IsStableUnderBaseChangeAlong (@IsAffineHom) t :=
    ⟨fun pb hf => isAffineHom_isStableUnderBaseChange.of_isPullback pb hf⟩
  have {i j : Iᵒᵖ} (f : i ⟶ j) : IsAffineHom (D.system.map f) := D.transition_affine f
  let J := Over (Opposite.op D.base)
  let F : J ⥤ Scheme.{u} := Over.post D.system ⋙ Over.pullback t ⋙ Over.forget T
  let c : Cone F := (Over.pullback t ⋙ Over.forget T).mapCone
    ((Over.conePost D.system (Opposite.op D.base)).obj D.limitCone)
  have : IsConnected J := IsCofiltered.isConnected J
  have hc : IsLimit c := isLimitOfPreserves (Over.pullback t ⋙ Over.forget T)
    (Over.isLimitConePost _ D.isLimit)
  have (j : J) : Nonempty (F.obj j) := by
    have : Nonempty I := ⟨D.base⟩
    obtain ⟨k, hjk, hbk, hk⟩ := Filter.frequently_atTop.mp H j.left.unop
    let q : Over (Opposite.op D.base) := Over.mk (homOfLE hbk).op
    let f : q ⟶ j := Over.homMk (homOfLE hjk).op (Subsingleton.elim _ _)
    exact Nonempty.map (F.map f)
      (Nonempty.map (pullbackSymmetry t (D.system.map (homOfLE hbk).op)).hom.base
        (by simpa [q] using hk))
  have {j k : J} (f : j ⟶ k) : IsAffineHom (F.map f) := by
    dsimp only [F, Functor.comp_map]
    exact MorphismProperty.overPullbackMap t ((Over.post D.system).map f)
      (D.transition_affine f.left)
  have (j : J) : CompactSpace (F.obj j) := by
    dsimp only [F, Functor.comp_obj]
    have : IsAffineHom (((Over.post D.system).obj j).hom) := D.transition_affine j.hom
    have : QuasiCompact (((Over.post D.system).obj j).hom) := inferInstance
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ t)
  exact hT.false
    (Nonempty.map (pullbackSymmetry (D.limitCone.π.app (Opposite.op D.base)) t).hom.base
      (by simpa [c] using Scheme.nonempty_of_isLimit F c hc)).some

/-- A constructible subset of an affine scheme is the set-theoretic image of a morphism from an
affine quasi-compact scheme. -/
lemma exists_affine_scheme_with_range {X : Scheme.{u}} [IsAffine X] {s : Set X}
    (hs : Topology.IsConstructible s) :
    ∃ (T : Scheme.{u}) (_ : IsAffine T) (_ : CompactSpace T) (t : T ⟶ X),
      Set.range t.base = s := by
  let e := X.isoSpec.hom.homeomorph
  have hs' : Topology.IsConstructible (e '' s) :=
    hs.image_of_isOpenEmbedding e.isOpenEmbedding (by rw [e.surjective.range_eq]; exact .univ)
  obtain ⟨S, inst, f, hf⟩ := PrimeSpectrum.exists_range_eq_of_isConstructible hs'
  let : CommRing S := inst
  refine ⟨Spec (.of S), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom f) ≫ X.isoSpec.inv, ?_⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  show X.isoSpec.inv.base '' Set.range (PrimeSpectrum.comap f) = s
  change Set.range (PrimeSpectrum.comap f) = e '' s at hf
  calc
    X.isoSpec.inv.base '' Set.range (PrimeSpectrum.comap f) =
        X.isoSpec.inv.base '' (e '' s) := by congr 1
    _ = s := by ext x; simp [e]

/-- **Stacks Project, Tag 05F4.** A locally constructible subset of a stage in a directed inverse
system contains the images of all sufficiently large stages if it contains the image of the
limit. -/
@[stacks 05F4]
lemma eventually_range_transition_subset_of_isLocallyConstructible
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : DescentSituation.{u, u} I)
    (E : Set (D.system.obj (op D.base)))
    (hE : Topology.IsLocallyConstructible E)
    (hlim : Set.range (D.limitCone.π.app (op D.base)).base ⊆ E) :
    ∀ᶠ i in atTop, ∃ h : D.base ≤ i,
      Set.range (D.system.map (homOfLE h).op).base ⊆ E := by
  let X := D.system.obj (op D.base)
  have : CompactSpace X := D.quasiCompact D.base
  have : QuasiSeparatedSpace X := D.quasiSeparated D.base
  obtain ⟨𝒰, h𝒰fin, h𝒰⟩ :=
    (isCompact_iff_finite_and_eq_biUnion_affineOpens (X := X) (U := ⊤)).mp isCompact_univ
  have hcover : ∀ x : X, ∃ U ∈ 𝒰, x ∈ (U : Set X) := by
    intro x
    have hx : x ∈ (⊤ : X.Opens) := trivial
    rw [h𝒰] at hx
    simpa using hx
  have hU : ∀ U ∈ 𝒰, ∀ᶠ i in atTop, ∀ h : D.base ≤ i,
      Set.range (D.system.map (homOfLE h).op).base ∩ (U : Set X) ⊆ E := by
    intro U hUmem
    have hconstructible : Topology.IsConstructible (U.1.ι.base ⁻¹' Eᶜ) := by
      simpa only [Set.preimage_compl] using
        (hE.preimage_of_isOpenEmbedding U.1.ι.isOpenEmbedding).isConstructible.compl
    obtain ⟨T, _, _, tU, htU⟩ := exists_affine_scheme_with_range hconstructible
    let t : T ⟶ X := tU ≫ U.1.ι
    have ht : Set.range t.base ⊆ Eᶜ := by
      rintro _ ⟨x, rfl⟩
      exact (htU ▸ Set.mem_range_self x : tU.base x ∈ U.1.ι.base ⁻¹' Eᶜ)
    have hpull : IsEmpty (pullback t (D.limitCone.π.app (op D.base)) : Scheme) :=
      Scheme.isEmpty_pullback_iff.2 (Set.disjoint_left.2 fun _ hxt hxl => ht hxt (hlim hxl))
    filter_upwards [eventually_isEmpty_pullback D T t hpull] with i hi
    intro h x hx
    by_contra hxE
    obtain ⟨y, hy⟩ : (⟨x, hx.2⟩ : U.1) ∈ Set.range tU.base := by
      rw [htU]
      exact hxE
    have hxt : x ∈ Set.range t.base := ⟨y, congrArg Subtype.val hy⟩
    exact Set.disjoint_left.mp (Scheme.isEmpty_pullback_iff.mp (hi h)) hxt hx.1
  filter_upwards [(h𝒰fin.eventually_all).2 hU, eventually_ge_atTop D.base] with i hi h
  refine ⟨h, fun x hx => ?_⟩
  obtain ⟨U, hUmem, hxU⟩ := hcover x
  exact hi U hUmem h ⟨hx, hxU⟩

end AlgebraicGeometry

end
