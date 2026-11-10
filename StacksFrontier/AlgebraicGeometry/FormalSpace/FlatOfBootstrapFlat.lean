module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatOfRepresentableFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableEtaleCancellationGeneral
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautChartRepresentability
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.Topology.Algebra.AdicTopology.FlatOfFlatQuotientMaps

/-!
# Flatness in the Bootstrap sense implies flatness of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of
formal algebraic spaces over `S`. **Stacks 0GCG** says that if `f` is representable by
algebraic spaces and flat in the Bootstrap sense of Stacks 03XZ, then `f` is flat in the sense
of Definition 0GCC.

Consider a commutative square with `U`, `V` affine formal algebraic spaces, `U ⟶ X` and
`V ⟶ Y` representable by algebraic spaces and étale, and `U ⟶ V` presented as `Spf (φ)` for a
continuous homomorphism `φ : A ⟶ C` of adic Noetherian topological rings. The proof has three
steps.

1. `φ` is taut. The chart map `U ⟶ V` is representable by algebraic spaces because `f` is
   (Stacks 0AN4), so its presenting homomorphism is taut (Stacks 0AN5).
2. For every weak ideal of definition `I` of `A`, the map `A ⧸ I → C ⧸ J(I)`, where `J(I)` is
   the closure of `φ(I)C`, is flat. Write `T = Spec (A ⧸ I)` and `W = Spec (C ⧸ J(I))`.
   Tautness makes `W = U ×_V T`. The fibre product `P = X ×_Y T` is
   `(V ×_Y X) ×_V T`, so `W = U ×_{V ×_Y X} P`. The map `U ⟶ V ×_Y X` is representable étale,
   because its composite with the étale projection `V ×_Y X ⟶ X` is `U ⟶ X`; hence so is its
   base change `W ⟶ P`. Then `W ⟶ P` is an étale chart of `P` lying over the identity chart of
   `T`, and the Bootstrap flatness of `f` at the point `T ⟶ Y` makes `W ⟶ T` flat.
3. `φ` is flat, by Stacks 0912
   (`RingHom.flat_of_isTaut_of_flat_quotientMap_closure`).

## Main results

* `AlgebraicGeometry.FormalSpace.isTautOnEveryChartMap_of_isRepresentableByAlgebraicSpacesULift`:
  step 1.
* `AlgebraicGeometry.FormalSpace.flat_quotientMap_closure_of_hasPropertyULift_flatPropertyULift`:
  step 2.
* `AlgebraicGeometry.FormalSpace.isFlat_of_hasPropertyULift_flatPropertyULift`:
  **Stacks 0GCG**.

## Implementation notes

The source uses Stacks 05B9 in step 2, to pass from flatness of `U ×_V (V ×_Y T) ⟶ T` to
flatness of `U ×_V (V ×_Y T) ⟶ V ×_Y T`, and then base changes along `T ⟶ V ×_Y T`. Here we
instead use cancellation of representable étale morphisms
(`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_comp'`), which makes `W` an étale chart of
`X ×_Y T` directly. Then flatness of `W ⟶ T` is a single instance of the every-étale-chart
condition, and no flatness of morphisms of algebraic spaces has to be composed or base changed.

The source states the lemma for locally Noetherian formal algebraic spaces. The proof does not
use this hypothesis, so it is omitted. Definition 0GCC already restricts to charts presented by
adic Noetherian rings.

## References

* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
* [Stacks Project, Tag 0912](https://stacks.math.columbia.edu/tag/0912)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0ANK](https://stacks.math.columbia.edu/tag/0ANK)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GCG](https://stacks.math.columbia.edu/tag/0GCG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The neighbourhoods of zero in an adic topological ring are countably generated, by the
powers of an ideal of definition. -/
private theorem isCountablyGenerated_nhds_zero_of_isAdic {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (h : TopologicalRing.IsAdic R) :
    (nhds (0 : R)).IsCountablyGenerated := by
  obtain ⟨⟨I, -, hI⟩, -⟩ := h
  exact hI.hasBasis_nhds_zero.isCountablyGenerated

/-- **Step 1 of Stacks 0GCG.** If `f : X ⟶ Y` is representable by algebraic spaces, then on
every affine representable étale square over `f` the homomorphism presenting the chart map is
taut. The chart map is representable by algebraic spaces (Stacks 0AN4), and a homomorphism
presenting a representable map of formal spectra of adic, hence countably indexed, rings is
taut (Stacks 0AN5). -/
theorem isTautOnEveryChartMap_of_isRepresentableByAlgebraicSpacesULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom) :
    IsTautOnEveryChartMap B S hS f := by
  intro U V hU hV a b t ha hb _ _ hsq A C _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E eU eV g hg
  have ht : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS t.hom :=
    isRepresentableOnEverySquare_of_isRepresentable' B S hS f hrep U V a b t
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hU)
      (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hV) ha hb hsq
  exact hasTautOnAffineChartMap_of_isRepresentableByAlgebraicSpacesULift B S hS t ht A C
    ⟨hA, isCountablyGenerated_nhds_zero_of_isAdic hAadic⟩
    ⟨Rig.weaklyAdmissible_of_isAdicRing hCadic, isCountablyGenerated_nhds_zero_of_isAdic hCadic⟩
    hA D E eU eV g hg

variable {B S hS}
variable {A C : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
  [IsLinearTopology C C]

/-- **Step 2 of Stacks 0GCG.** Let `f : X ⟶ Y` be representable by algebraic spaces and flat in
the Bootstrap sense, and let `U ⟶ X`, `V ⟶ Y` be representable étale with a map `t : U ⟶ V`
over `f`, presented by a taut continuous homomorphism `φ : A ⟶ C` of weakly admissible
topological rings. Then for every weak ideal of definition `I` of `A` the induced ring map
`A ⧸ I → C ⧸ J(I)`, with `J(I)` the closure of `φ(I)C`, is flat.

The stage `W = Spec (C ⧸ J(I))` is `U ×_V T` for `T = Spec (A ⧸ I)`, by tautness. It maps to
`X ×_Y T = (V ×_Y X) ×_V T` by a base change of `U ⟶ V ×_Y X`, which is representable étale
by cancellation against the étale projection `V ×_Y X ⟶ X`. So `W` is an étale chart of
`X ×_Y T` over the identity chart of `T`, and Bootstrap flatness makes `W ⟶ T` flat. -/
theorem flat_quotientMap_closure_of_hasPropertyULift_flatPropertyULift
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS (Space.flatPropertyULift.{u + 1} B S hS)
      f.hom hrep)
    {U V : FppfSheaf B S hS} (a : U ⟶ X) (b : V ⟶ Y) (t : U ⟶ V)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsq : a ≫ f = t ≫ b)
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (D : QuotientSystem B S hS A) (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E)
    (eV : V ≅ formalSpectrum D) (g : ContinuousHom D E)
    (hg : t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv) (hgt : RingHom.IsTaut g.toRingHom)
    (I : Ideal A) (hI : TopologicalRing.IsWeakIdealOfDefinition I) :
    (Ideal.quotientMap (Ideal.closure (I.map g.toRingHom)) g.toRingHom
      (Ideal.map_le_iff_le_comap.mp subset_closure)).Flat := by
  obtain ⟨⟨K, hKw⟩, hKeq, hIK, hst⟩ :=
    isPullback_formalSpectrumMap_stage_of_isTaut B S hS hA hC D E g hgt ⟨I, hI⟩
  subst hKeq
  set y := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  set G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  set k := (BigAffineFppf.inclusion B S hS).map
    (g.stageMap ⟨I, hI⟩ ⟨Ideal.closure (I.map g.toRingHom), hKw⟩ hIK) with hk
  -- The stage square, transported to `U` and `V`.
  set vT := formalSpectrumInclusion D ⟨I, hI⟩ ≫ eV.inv
  set uW := formalSpectrumInclusion E ⟨Ideal.closure (I.map g.toRingHom), hKw⟩ ≫ eU.inv
  have hW : IsPullback uW (y.map k) t vT :=
    hst.of_iso (Iso.refl _) eU.symm (Iso.refl _) eV.symm
      (by rw [Iso.refl_hom, Category.id_comp]; rfl)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by rw [hg, Iso.symm_hom, Iso.symm_hom]; exact (eU.inv_hom_id_assoc _).symm)
      (by rw [Iso.refl_hom, Category.id_comp]; rfl)
  -- The map `U ⟶ V ×_Y X` is representable étale.
  set m : U ⟶ pullback b f := pullback.lift t a hsq.symm
  have hmet : IsRepresentableEtale B S hS m :=
    isRepresentableEtale_of_comp' B S hS m (pullback.snd b f)
      (isRepresentableEtale_pullback_snd B S hS b f hb) (by rw [pullback.lift_snd]; exact ha)
  -- Its base change `W ⟶ (V ×_Y X) ×_V T`.
  set φ : y.obj _ ⟶ pullback vT (pullback.fst b f) :=
    pullback.lift (y.map k) (uW ≫ m) (by rw [Category.assoc, pullback.lift_fst]; exact hW.w.symm)
    with hφ
  have hφsq : IsPullback uW φ m (pullback.snd vT (pullback.fst b f)) := by
    refine IsPullback.of_bot ?_ (pullback.lift_snd _ _ _).symm
      (IsPullback.of_hasPullback vT (pullback.fst b f)).flip
    rw [pullback.lift_fst, pullback.lift_fst]
    exact hW
  have hφet : IsRepresentableEtale B S hS φ :=
    isRepresentableEtale_of_isPullback B S hS hφsq hmet
  -- The fibre product `(V ×_Y X) ×_V T` is `X ×_Y T`, at the level of presheaves.
  set iT := sheafifiedYonedaObjIso B S hS
    ((BigAffineFppf.inclusion B S hS).obj (D.stage ⟨I, hI⟩))
  set iW := sheafifiedYonedaObjIso B S hS
    ((BigAffineFppf.inclusion B S hS).obj
      (E.stage ⟨Ideal.closure (I.map g.toRingHom), hKw⟩))
  set ξ := iT.hom ≫ G.map (vT ≫ b) with hξ
  have hP : IsPullback (pullback.fst vT (pullback.fst b f))
      (pullback.snd vT (pullback.fst b f) ≫ pullback.snd b f) (vT ≫ b) f :=
    (IsPullback.of_hasPullback vT (pullback.fst b f)).paste_vert
      (IsPullback.of_hasPullback b f)
  have hPp : IsPullback (G.map (pullback.fst vT (pullback.fst b f)) ≫ iT.inv)
      (G.map (pullback.snd vT (pullback.fst b f) ≫ pullback.snd b f)) ξ (G.map f) :=
    (hP.map G).of_iso (Iso.refl _) iT.symm (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.id_comp, Iso.symm_hom])
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      (by rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, hξ, Iso.inv_hom_id_assoc])
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  -- The étale chart `W ⟶ X ×_Y T`.
  set c₀ := iW.hom ≫ G.map φ with hc₀def
  have sq₀ : IsPullback iW.hom c₀ (G.map φ) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [c₀]⟩
  have hc₀ : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) c₀ :=
    relative_etale_of_schemeSource B S hS _ c₀
      (Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS iW.hom c₀ (G.map φ)
        (𝟙 _) sq₀ hφet.1)
      (isEtaleULift_pullback_fst_of_isPullback B S hS sq₀ hφet.2)
  have hc : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1})
      (c₀ ≫ hPp.isoPullback.hom) :=
    MorphismProperty.RespectsIso.postcomp _ hPp.isoPullback.hom c₀ hc₀
  have hnat : (uliftYoneda.{u + 1}).map k ≫ iT.hom = iW.hom ≫ G.map (y.map k) :=
    sheafifiedYonedaObjIso_naturality B S hS k
  have hchart : (uliftYoneda.{u + 1}).map k ≫ 𝟙 _ =
      (c₀ ≫ hPp.isoPullback.hom) ≫ pullback.fst ξ (G.map f) := by
    rw [Category.comp_id, Category.assoc, hPp.isoPullback_hom_fst, hc₀def, Category.assoc,
      ← Category.assoc (G.map φ), ← G.map_comp, hφ, pullback.lift_fst, ← Category.assoc,
      ← hnat, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hfl : Space.IsFlatULift.{u + 1} B S hS (pullback.fst ξ (G.map f)) := hflat _ ξ
  have hk' := hfl _ _ _ (𝟙 _) k hc (Space.relative_id_etale.{u + 1} B S hS _) hchart
  rw [hk] at hk'
  exact AlgebraicGeometry.HasRingHomProperty.Spec_iff.mp
    (show AlgebraicGeometry.Flat (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (Ideal.closure (I.map g.toRingHom)) g.toRingHom hIK))) from hk')

/-- **Stacks 0GCG.** A morphism `f : X ⟶ Y` of formal algebraic spaces over `S` which is
representable by algebraic spaces and flat in the Bootstrap sense of Stacks 03XZ is flat in the
sense of Definition 0GCC.

On an affine representable étale square over `f`, the homomorphism `φ` presenting the chart map
is taut because `f` is representable. Bootstrap flatness of `f` makes `φ` flat modulo every
weak ideal of definition of its source, and Stacks 0912 concludes that `φ` is flat. The source
assumes `X` and `Y` locally Noetherian; the proof does not use this. -/
@[stacks 0GCG]
theorem isFlat_of_hasPropertyULift_flatPropertyULift {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom)
    (hflat : Space.HasPropertyULift.{u + 1} B S hS (Space.flatPropertyULift.{u + 1} B S hS)
      f.hom hrep) :
    IsFlat B S hS f := by
  intro U V hU hV a b t ha hb hae hbe hsq A' C' _ _ _ _ _ _ _ _ _ _ hAadic hCadic hA D E
    eU eV g hg
  have hgt : RingHom.IsTaut g.toRingHom :=
    isTautOnEveryChartMap_of_isRepresentableByAlgebraicSpacesULift B S hS f hrep U V hU hV a b
      t ha hb hae hbe hsq A' C' hAadic hCadic hA D E eU eV g hg
  exact RingHom.flat_of_isTaut_of_flat_quotientMap_closure g.toRingHom hAadic hCadic
    hgt fun I hI ↦
      flat_quotientMap_closure_of_hasPropertyULift_flatPropertyULift f hrep hflat a b t
        ⟨ha, hae⟩ ⟨hb, hbe⟩ hsq hA (Rig.weaklyAdmissible_of_isAdicRing hCadic) D E eU eV g hg
        hgt I hI

end AlgebraicGeometry.FormalSpace

end
