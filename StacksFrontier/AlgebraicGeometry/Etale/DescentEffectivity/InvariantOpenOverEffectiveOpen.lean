module

public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetSingleMorphism
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.InvariantOpenFromBase
public import StacksFrontier.AlgebraicGeometry.Etale.DescentEffectivity.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair

/-!
# An invariant open lying over an effective open of the base is effective

Let `f : X ⟶ S` be a surjective universally closed morphism of schemes (for instance a
surjective integral morphism), let `(V, φ)` be a descent datum relative to `X/S` with `V ⟶ X`
étale, and let `S' ⊆ S` be an open over which the datum is étale effective, descended by a
scheme `U'` étale over `S'`. If `W ⊆ V` is an open invariant under `φ` whose image in `S` lies
in `S'`, then the restriction of the datum to `W` is étale effective over the whole of `S`: it
is descended by an open subscheme of `U'`, viewed as a scheme over `S` through `S' ⊆ S`.

The open of `U'` is the image of `W` under the projection `p : V_{S'} ⟶ U'`. That projection is
a base change of `f`, hence surjective and universally closed, so it is a quotient map of the
underlying spaces; and `W` is saturated for it, because invariance of `W` under `φ` says that
the two preimages of `W` in `V_{S'} ×_{U'} V_{S'} ≅ V_{S'} ×_S X` agree. A saturated open has
open image under a surjective closed map. This is the descent of opens of
[Stacks, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0) with the fpqc hypothesis replaced
by universal closedness: what is used of the covering is only that it is submersive.

In the henselian endgame of [Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP), with
`S = Spec A`, `Z = V(I)` and `S' ⊇ S ∖ Z`, this applies to the invariant piece `V_away` of the
splitting of Tag 0BTN, which has no point over `Z`: the source's *"`V_away` corresponds to an
open and closed subscheme `U'_fin` of `U'`"*, read as effectivity of the restricted datum.

## Main definitions

* `AlgebraicGeometry.DescentDatum.Descended.shrinkOfPreimageEq`: the descended scheme of the
  restriction of a datum to a smaller invariant open, given an open of the descended scheme
  whose preimage is that smaller open.

## Main results

* `AlgebraicGeometry.existsUnique_opens_preimage_eq_of_universallyClosed_of_surjective`: an open
  whose two preimages in `T' ×_T T'` agree is the preimage of a unique open of `T`, along a
  surjective universally closed morphism `T' ⟶ T`.
* `AlgebraicGeometry.DescentDatum.Descended.existsUnique_opens_preimage_eq_of_universallyClosed`:
  along a surjective universally closed `f`, an invariant open of a datum is the preimage of a
  unique open of any scheme descending it.
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_restrictOpen_of_le_baseOpens`: **an invariant
  open lying over an open of the base over which the datum is étale effective is étale
  effective.**
* `AlgebraicGeometry.DescentDatum.isEtaleEffective_restrictOpen_of_isEmpty_closedFiber`: the
  case `S = Spec A` with an invariant open having no point over `V(I)` and effectivity over an
  open containing `Spec A ∖ V(I)`.

## Implementation notes

The descended scheme of the restriction is built from the descended scheme over `S'` exactly as
`AlgebraicGeometry.DescentDatum.Descended.shrink` builds it, but with the descended open passed
in together with the equation identifying its preimage. `shrink` produces that open itself by
fpqc descent of opens, which needs `f` flat; along an integral morphism the open is produced by
`AlgebraicGeometry.DescentDatum.Descended.existsUnique_opens_preimage_eq_of_universallyClosed`
instead.

No hypothesis of quasi-compactness or separatedness is needed, and the henselian property of
the pair `(A, I)` plays no role in the second result: only the emptiness of the closed fibre of
`W` is used.

## References

* [Stacks Project, Tag 03N0](https://stacks.math.columbia.edu/tag/03N0)
* [Stacks Project, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP)
-/

@[expose] public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

/-! ### Descent of opens along a surjective universally closed morphism -/

/-- **An open subset descends along a surjective universally closed morphism.** Let
`g : T' ⟶ T` be surjective and universally closed and let `W' ⊆ T'` be open with
`pr₀⁻¹(W') = pr₁⁻¹(W')` in `T' ×_T T'`. Then there is a unique open `W ⊆ T` with
`W' = g⁻¹(W)`, namely the image of `W'`: it is saturated, and its complement is the image of the
closed complement of `W'`. -/
theorem existsUnique_opens_preimage_eq_of_universallyClosed_of_surjective {T' T : Scheme.{u}}
    (g : T' ⟶ T) [Surjective g] [UniversallyClosed g] (W' : T'.Opens)
    (hcompat : (pullback.fst g g).base ⁻¹' (W' : Set T') =
      (pullback.snd g g).base ⁻¹' (W' : Set T')) :
    ∃! W : T.Opens, g ⁻¹ᵁ W = W' := by
  have hpre : g.base ⁻¹' (g.base '' W') = W' :=
    preimage_image_eq_of_preimage_fst_eq_preimage_snd g hcompat
  have hopen : IsOpen (g.base '' (W' : Set T')) := by
    have hcompl : g.base '' ((W' : Set T')ᶜ) = (g.base '' (W' : Set T'))ᶜ := by
      conv_lhs => rw [← hpre]
      rw [← Set.preimage_compl, Set.image_preimage_eq _ g.surjective]
    rw [← isClosed_compl_iff, ← hcompl]
    exact g.isClosedMap _ W'.isOpen.isClosed_compl
  refine ⟨⟨_, hopen⟩, TopologicalSpace.Opens.ext hpre, fun V hV ↦ TopologicalSpace.Opens.ext ?_⟩
  subst hV
  exact (Set.image_preimage_eq _ g.surjective).symm

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S}

attribute [local implicit_reducible] restrictOpen

namespace Descended

variable {D : DescentDatum f}

/-- **An invariant open descends to the base along a surjective universally closed morphism.**
For `f` surjective and universally closed, an open of `V` invariant under the gluing isomorphism
is the preimage of exactly one open of a scheme descending the datum. The projection of the
descended scheme is a base change of `f`, hence surjective and universally closed, and the two
preimages of the open in `V ×_U V ≅ V ×_S X` agree by invariance. -/
theorem existsUnique_opens_preimage_eq_of_universallyClosed [Surjective f] [UniversallyClosed f]
    (Q : D.Descended) (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) :
    ∃! W₀ : Q.base.left.Opens, Q.proj ⁻¹ᵁ W₀ = W := by
  have := Q.universallyClosed_proj
  have hpb := Q.isPullback_legs
  have hesurj : Function.Surjective hpb.isoPullback.hom.base :=
    (Scheme.homeoOfIso hpb.isoPullback).surjective
  refine existsUnique_opens_preimage_eq_of_universallyClosed_of_surjective
    Q.proj W (hesurj.preimage_injective ?_)
  have hcomp (g : pullback Q.proj Q.proj ⟶ D.over.left) :
      hpb.isoPullback.hom.base ⁻¹' (g.base ⁻¹' (W : Set _)) =
      (hpb.isoPullback.hom ≫ g).base ⁻¹' (W : Set _) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  rw [hcomp, hcomp, hpb.isoPullback_hom_fst, hpb.isoPullback_hom_snd]
  exact DescentData.preimage_transition_snd_eq_preimage_fst D W hW

/-! ### The descended scheme of a smaller invariant open, from a given open of the base -/

section ShrinkOfPreimageEq

variable {W : D.over.left.Opens} {hW : D.IsTransitionInvariant W}
  (Q : (D.restrictOpen W hW).Descended) {Z : D.over.left.Opens}

/-- A smaller open `Z ⊆ W`, identified with the preimage under the projection of an open `O` of
the descended scheme whose preimage is `Z`. -/
def shrinkIsoOfPreimageEq (hle : Z ≤ W) (O : Q.base.left.Opens)
    (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) : Z.toScheme ≅ (Q.proj ⁻¹ᵁ O).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.over.left.homOfLE hle) (Q.proj ⁻¹ᵁ O).ι
    (by simp only [← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι,
      Scheme.opensRange_homOfLE, hO])

/-- That identification is the inclusion of the smaller open. -/
@[reassoc]
lemma shrinkIsoOfPreimageEq_hom_ι (hle : Z ≤ W) (O : Q.base.left.Opens)
    (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) :
    (Q.shrinkIsoOfPreimageEq hle O hO).hom ≫ (Q.proj ⁻¹ᵁ O).ι = D.over.left.homOfLE hle :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The projection of the smaller open onto the open `O` of the descended scheme. -/
@[implicit_reducible]
def shrinkProjOfPreimageEq (hle : Z ≤ W) (O : Q.base.left.Opens)
    (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) : Z.toScheme ⟶ O.toScheme :=
  (Q.shrinkIsoOfPreimageEq hle O hO).hom ≫ (Q.proj ∣_ O)

/-- **The characterisation of the restricted projection**: followed by the inclusion of `O` it
is the inclusion of the smaller open followed by the projection. -/
@[reassoc]
lemma shrinkProjOfPreimageEq_comp_ι (hle : Z ≤ W) (O : Q.base.left.Opens)
    (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) :
    Q.shrinkProjOfPreimageEq hle O hO ≫ O.ι = D.over.left.homOfLE hle ≫ Q.proj := by
  rw [shrinkProjOfPreimageEq, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    Q.shrinkIsoOfPreimageEq_hom_ι]

/-- **The descended scheme of the restriction to a smaller invariant open `Z ⊆ W`**, given an
open `O` of the scheme descending the restriction to `W` whose preimage is `Z`: it is the open
subscheme `O`, with the restricted projection. No hypothesis on `f` is needed, the open being
given rather than descended. -/
@[implicit_reducible]
def shrinkOfPreimageEq (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W) (O : Q.base.left.Opens)
    (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) : (D.restrictOpen Z hZ).Descended where
  base := Over.mk (O.ι ≫ Q.base.hom)
  proj := Q.shrinkProjOfPreimageEq hle O hO
  isPullback := by
    have s : IsPullback (Q.shrinkProjOfPreimageEq hle O hO) (D.over.left.homOfLE hle)
        O.ι Q.proj :=
      (isPullback_morphismRestrict Q.proj O).of_iso'
        (Q.shrinkIsoOfPreimageEq hle O hO) (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by rw [Iso.refl_hom, Category.comp_id]; rfl)
        (by rw [Iso.refl_hom, Category.comp_id]; exact Q.shrinkIsoOfPreimageEq_hom_ι hle O hO)
        (by simp) (by simp)
    have h := s.paste_vert Q.isPullback.flip
    rw [show D.over.left.homOfLE hle ≫ (D.restrictOpen W hW).over.hom =
        (D.restrictOpen Z hZ).over.hom from by
      change D.over.left.homOfLE hle ≫ W.ι ≫ D.over.hom = Z.ι ≫ D.over.hom
      rw [← Category.assoc, Scheme.homOfLE_ι]] at h
    exact h.flip
  proj_invariant := by
    refine (cancel_mono O.ι).mp ?_
    rw [Category.assoc, Category.assoc, Q.shrinkProjOfPreimageEq_comp_ι, Category.assoc,
      Q.shrinkProjOfPreimageEq_comp_ι]
    exact comp_proj_invariant (D.restrictOpenMono hZ hW hle) Q

/-- The scheme descending the restriction to the smaller open is the open `O`. -/
@[simp]
lemma shrinkOfPreimageEq_base (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W)
    (O : Q.base.left.Opens) (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) :
    (Q.shrinkOfPreimageEq hZ hle O hO).base = Over.mk (O.ι ≫ Q.base.hom) := rfl

/-- The projection of the scheme descending the restriction to the smaller open. -/
@[simp]
lemma shrinkOfPreimageEq_proj (hZ : D.IsTransitionInvariant Z) (hle : Z ≤ W)
    (O : Q.base.left.Opens) (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) :
    (Q.shrinkOfPreimageEq hZ hle O hO).proj = Q.shrinkProjOfPreimageEq hle O hO := rfl

/-- The scheme descending the restriction to the smaller open is étale over `S` when the scheme
descending the restriction to `W` is, being an open subscheme of it. -/
instance etale_shrinkOfPreimageEq_base_hom [Etale Q.base.hom] (hZ : D.IsTransitionInvariant Z)
    (hle : Z ≤ W) (O : Q.base.left.Opens) (hO : Q.proj ⁻¹ᵁ O = W.ι ⁻¹ᵁ Z) :
    Etale (Q.shrinkOfPreimageEq hZ hle O hO).base.hom := by
  change Etale (O.ι ≫ Q.base.hom)
  infer_instance

end ShrinkOfPreimageEq

end Descended

/-! ### Effectivity of an invariant open lying over an effective open of the base -/

/-- **An invariant open lying over an open of the base over which the datum is étale effective
is étale effective.** Let `f : X ⟶ S` be surjective and universally closed, let `(V, φ)` be a
descent datum relative to `f` with `V ⟶ X` étale, étale effective over an open `T ⊆ S`, and let
`W ⊆ V` be an invariant open whose image in `S` lies in `T`. Then the restriction of the datum
to `W` is étale effective over `S`: it is descended by the open of the scheme `U'` descending
the datum over `T` onto which `W` projects, viewed over `S`. -/
theorem isEtaleEffective_restrictOpen_of_le_baseOpens [Surjective f] [UniversallyClosed f]
    (D : DescentDatum f) [Etale D.over.hom] {T : S.Opens} (hT : (D.baseDatum T).IsEtaleEffective)
    (W : D.over.left.Opens) (hW : D.IsTransitionInvariant W) (hle : W ≤ D.baseOpens T) :
    (D.restrictOpen W hW).IsEtaleEffective := by
  let C := D.baseChartOfIsEtaleEffective T hT
  have : Etale C.descended.base.hom := inferInstanceAs (Etale (C.base.hom ≫ T.ι))
  obtain ⟨O, hO, -⟩ := C.descended.existsUnique_opens_preimage_eq_of_universallyClosed
    ((D.baseOpens T).ι ⁻¹ᵁ W) (Descended.isTransitionInvariant_ι_preimage hW)
  exact (C.descended.shrinkOfPreimageEq hW hle O hO).isEtaleEffective

/-- **An invariant open with no point over the closed fibre of `Spec A ⟶ Spec (A ⧸ I)` is étale
effective, as soon as the datum is étale effective over an open containing
`Spec A ∖ V(I)`.** This is
`AlgebraicGeometry.DescentDatum.isEtaleEffective_restrictOpen_of_le_baseOpens` for
`S = Spec A`: an open of `V` whose base change to `Spec (A ⧸ I)` is empty lies over
`Spec A ∖ V(I)`. In the henselian endgame of
[Stacks, Tag 0BTP](https://stacks.math.columbia.edu/tag/0BTP) it is applied to the piece
`V_away` of the splitting of Tag 0BTN. -/
theorem isEtaleEffective_restrictOpen_of_isEmpty_closedFiber {A : Type u} [CommRing A]
    (I : Ideal A) {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of A)} [Surjective f]
    [UniversallyClosed f] (D : DescentDatum f) [Etale D.over.hom]
    {T : (Spec (CommRingCat.of A)).Opens}
    (hT : (PrimeSpectrum.zeroLocus (I : Set A))ᶜ ⊆ (T : Set (Spec (CommRingCat.of A))))
    (heff : (D.baseDatum T).IsEtaleEffective) (W : D.over.left.Opens)
    (hW : D.IsTransitionInvariant W)
    (hempty : IsEmpty (pullback ((W.ι ≫ D.over.hom) ≫ f)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) : Scheme.{u})) :
    (D.restrictOpen W hW).IsEtaleEffective := by
  refine D.isEtaleEffective_restrictOpen_of_le_baseOpens heff W hW fun w hw ↦ ?_
  have hdisj := Scheme.isEmpty_pullback_iff.mp hempty
  rw [range_spec_map_quotient_mk I] at hdisj
  exact hT fun hz ↦ Set.disjoint_left.mp hdisj ⟨⟨w, hw⟩, rfl⟩ hz

end DescentDatum

end AlgebraicGeometry

end
