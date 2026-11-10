module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.FiniteUnramified
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.QuasiFiniteEtaleLocalisation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.OpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksCore.Tactic.StacksAttribute

/-!
# Unramified points are étale-locally cut out by closed immersions

Let `f : X ⟶ S` be a morphism of schemes and let `x₁, …, xₙ` be distinct points of `X` with a
common image `s`. If `f` is unramified at each `xᵢ`, then after a single étale base change
`U ⟶ S` around `s` the points of the base change `X ×_S U` lying over `s` and above the `xᵢ` are
covered by finitely many open subschemes `V_{i,j} ⊆ X ×_S U`, each a closed subscheme of `U`
through the distinguished point of `U`, and two different ones never meet in the distinguished
fibre.

The proof replaces `X` by the open locus of unramifiedness, which makes `f` locally of finite
type, applies the étale localisation of quasi-finite morphisms
(`AlgebraicGeometry.exists_etale_finite_opens_of_isolated_fiber_points`) to obtain finite open
neighbourhoods of the chosen points, and shrinks the étale neighbourhood so that each of these
finitely many finite morphisms becomes a closed immersion, by
`AlgebraicGeometry.exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton`.

## Main results

* `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict_of_le`: a property local at the target
  passes from a restriction to the restriction to a smaller open set.
* `AlgebraicGeometry.unramified_ι_comp_of_forall_unramifiedAt`: an open subscheme all of whose
  points are points of unramifiedness is unramified over the target.
* `AlgebraicGeometry.exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt` is the
  theorem described above.

## Implementation notes

The open subschemes are indexed by the pairs `⟨i, j⟩` of `Σ i : Fin n, Fin (m i)`. Passing
through the distinguished point, meeting one another and covering the chosen fibre are all
expressed on points of the base change rather than on its fibre over the distinguished point,
which keeps the statement free of the identifications between a fibre and a pullback.

## References

* [Stacks Project, Tag 04HH](https://stacks.math.columbia.edu/tag/04HH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace IsZariskiLocalAtTarget

/-- A property of morphisms of schemes which is local at the target and holds for the restriction
of a morphism over an open set holds for the restriction over any smaller open set. -/
public theorem restrict_of_le {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {U V : Y.Opens} (hUV : U ≤ V) (hf : P (f ∣_ V)) :
    P (f ∣_ U) := by
  have himage : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr hUV
  exact (P.arrow_mk_iso_iff (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U) ≪≫
    morphismRestrictEq f himage)).mp (IsZariskiLocalAtTarget.restrict hf _)

end IsZariskiLocalAtTarget

/-- Equal morphisms of schemes agree on points. -/
private theorem hom_apply_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (x : X) :
    f x = g x := by
  rw [h]

/-- An affine open `U` of the source lying over an affine open `V` of the target on which the map
of sections is unramified is unramified over the target: the composite `U ⟶ X ⟶ S` is an
unramified morphism. -/
private theorem unramified_ι_comp_of_appLE {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens}
    {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (hAlg : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
      Algebra.Unramified Γ(S, V) Γ(X, U)) :
    Unramified (U.ι ≫ f) := by
  have hι : Unramified V.ι := by
    rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
    exact ⟨inferInstance, inferInstance⟩
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have hres : Unramified (f.resLE V U e) := by
    rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
    exact ⟨(HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
        ((RingHom.finiteType_respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f V U e)).2 hAlg.finiteType),
      (HasRingHomProperty.iff_of_isAffine (P := @FormallyUnramified)).2
        ((RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff
          (arrowResLEAppIso f V U e)).2 hAlg.formallyUnramified)⟩
  rw [← Scheme.Hom.resLE_comp_ι f e]
  exact MorphismProperty.comp_mem @Unramified _ _ hres hι

/-- An open subscheme of the source all of whose points are points of unramifiedness is
unramified over the target. In particular this applies to the open unramified locus
`AlgebraicGeometry.isOpen_setOf_unramifiedAt`. -/
public theorem unramified_ι_comp_of_forall_unramifiedAt {X S : Scheme.{u}} (f : X ⟶ S)
    (W : X.Opens) (hW : ∀ x ∈ W, UnramifiedAt f x) : Unramified (W.ι ≫ f) := by
  classical
  choose A hA hAmem B hB hAB hAlg using fun y : W.toScheme => hW y.1 y.2
  have : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := _)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Unramified.{u})
    (U := fun y : W.toScheme => W.ι ⁻¹ᵁ A y) ?_ fun y => ?_
  · exact top_le_iff.mp fun z _ => Opens.mem_iSup.mpr ⟨z, hAmem z⟩
  · have hrange : Set.range ((W.ι ⁻¹ᵁ A y).ι ≫ W.ι) ⊆ Set.range (A y).ι := by
      rintro - ⟨z, rfl⟩
      exact ⟨⟨W.ι ((W.ι ⁻¹ᵁ A y).ι z), z.2⟩, rfl⟩
    rw [← Category.assoc, ← IsOpenImmersion.lift_fac (A y).ι _ hrange, Category.assoc]
    exact IsZariskiLocalAtSource.comp
      (unramified_ι_comp_of_appLE f (hA y) (hB y) (hAB y) (hAlg y)) _

/-- **Stacks Project, Tag 04HH.** After a single étale base change, finitely many distinct points
of one fibre at which a morphism of schemes is unramified are covered, in that fibre, by open
subschemes which are closed immersions over the new base, pass through the distinguished point,
and pairwise avoid one another there. -/
@[stacks 04HH]
public theorem exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (x : Fin n → X) (s : S)
    (hx : ∀ i, f (x i) = s) (hx_injective : Function.Injective x)
    (hunramified : ∀ i, UnramifiedAt f (x i)) :
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (V : (Σ i, Fin (m i)) → (pullback f U.toBase).Opens),
      (∀ a, IsClosedImmersion ((V a).ι ≫ pullback.snd f U.toBase) ∧
        ∃ y : (pullback f U.toBase : Scheme.{u}),
          y ∈ V a ∧ (pullback.snd f U.toBase) y = U.point) ∧
      (∀ a b, a ≠ b → ∀ y : (pullback f U.toBase : Scheme.{u}),
        y ∈ V a → y ∈ V b → (pullback.snd f U.toBase) y ≠ U.point) ∧
      (∀ (i : Fin n) (y : (pullback f U.toBase : Scheme.{u})),
        (pullback.snd f U.toBase) y = U.point →
        (pullback.fst f U.toBase) y = x i →
        ∃ j : Fin (m i), y ∈ V ⟨i, j⟩) := by
  classical
  -- Replace `X` by the open locus of unramifiedness, over which `f` is unramified.
  let W : X.Opens := ⟨{z : X | UnramifiedAt f z}, isOpen_setOf_unramifiedAt f⟩
  have hW : ∀ i, x i ∈ W := hunramified
  let g : W.toScheme ⟶ S := W.ι ≫ f
  have : Unramified g := unramified_ι_comp_of_forall_unramifiedAt f W fun _ hz => hz
  let x' : Fin n → W.toScheme := fun i => ⟨x i, hW i⟩
  have hx'_isolated : ∀ i, IsIsolatedPoint (g.asFiber (x' i)) := fun i =>
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp (g.quasiFiniteAt (x' i))
  obtain ⟨U, m, V₀, v, hfinite, hinjective, hcover⟩ :=
    exists_etale_finite_opens_of_isolated_fiber_points g n s x' hx
      (fun i j hij => hx_injective (congrArg Subtype.val hij)) hx'_isolated
  -- The base change of `g` along the étale neighbourhood, and its restrictions to the `V₀`.
  let q := pullback.snd g U.toBase
  have hq : Unramified q :=
    unramified_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback g U.toBase) ‹_›
  have : IsZariskiLocalAtSource (@Unramified.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := _)
  let A := Σ i : Fin n, Fin (m i)
  let gA (a : A) := (V₀ a.1 a.2).ι ≫ q
  -- Each `gA a` is finite and unramified with a single point over the distinguished point, so it
  -- is a closed immersion over some open neighbourhood `Oa a` of that point.
  have hshrink (a : A) : ∃ O : U.scheme.Opens, U.point ∈ O ∧ IsClosedImmersion (gA a ∣_ O) := by
    obtain ⟨hfin, hfiber, _, _, _, hpure⟩ := hfinite a.1 a.2
    have : IsFinite (gA a) := hfin
    have : Unramified (gA a) := IsZariskiLocalAtSource.comp hq (V₀ a.1 a.2).ι
    exact exists_open_restrict_isClosedImmersion_of_finite_unramified_fiber_eq_singleton
      (gA a) U.point (v a.1 a.2) hfiber hpure
  choose Oa hOa hclosed using hshrink
  let O : U.scheme.Opens := ⨅ a : A, Oa a
  have hO : U.point ∈ O := by
    change U.point ∈ (O : Set U.scheme)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr hOa
  let Unew : EtaleNeighborhood S s :=
    { scheme := O.toScheme
      point := ⟨U.point, hO⟩
      toBase := O.ι ≫ U.toBase
      map_point := by
        change U.toBase (O.ι ⟨U.point, hO⟩) = s
        simpa using U.map_point }
  -- Three identifications of base changes: `Pnew` is the base change of `g` along `Unew`, which
  -- is both the base change of `q` along `O.ι` and an open subscheme of the base change `Pfull`
  -- of `f` along `Unew`.
  let Pold := pullback g U.toBase
  let Pmid := pullback q O.ι
  let Pnew := pullback g Unew.toBase
  let Pfull := pullback f Unew.toBase
  let eMid : Pmid ≅ Pnew := pullbackLeftPullbackSndIso g U.toBase O.ι
  let eW : pullback W.ι (pullback.fst f Unew.toBase) ≅ Pnew :=
    pullbackRightPullbackFstIso f Unew.toBase W.ι
  let j₂ : Pnew ⟶ Pold :=
    pullback.map g Unew.toBase g U.toBase (𝟙 W.toScheme) O.ι (𝟙 S) (by simp) (by simp [Unew])
  let j₀ : Pnew ⟶ Pfull := eW.inv ≫ pullback.snd W.ι (pullback.fst f Unew.toBase)
  let k₀ (a : A) : pullback (gA a) O.ι ⟶ Pmid :=
    pullback.map (gA a) O.ι q O.ι (V₀ a.1 a.2).ι (𝟙 O.toScheme) (𝟙 U.scheme) (by simp [gA])
      (by simp)
  have : ∀ a : A, IsOpenImmersion (k₀ a) := fun a => by dsimp [k₀]; infer_instance
  have : IsOpenImmersion j₀ := by dsimp [j₀]; infer_instance
  let k (a : A) : pullback (gA a) O.ι ⟶ Pfull := k₀ a ≫ eMid.hom ≫ j₀
  have : ∀ a : A, IsOpenImmersion (k a) := fun a => by dsimp [k]; infer_instance
  let V : A → Pfull.Opens := fun a => (k a).opensRange
  -- The second projection of `Pfull` restricted to `V a` is the base change of `gA a` along
  -- `O.ι`, hence a closed immersion.
  have hcomp (a : A) : k a ≫ pullback.snd f Unew.toBase = pullback.snd (gA a) O.ι := by
    dsimp [k]
    calc
      _ = k₀ a ≫ eMid.hom ≫ pullback.snd g Unew.toBase := by
        dsimp [j₀, pullback.map]
        simp only [Category.assoc]
        rw [pullbackRightPullbackFstIso_inv_snd_snd f Unew.toBase W.ι]
      _ = k₀ a ≫ pullback.snd q O.ι := by
        change k₀ a ≫ (pullbackLeftPullbackSndIso g U.toBase O.ι).hom ≫
          pullback.snd g (O.ι ≫ U.toBase) = k₀ a ≫ pullback.snd (pullback.snd g U.toBase) O.ι
        rw [pullbackLeftPullbackSndIso_hom_snd g U.toBase O.ι]
      _ = pullback.snd (gA a) O.ι := by
        dsimp [k₀, pullback.map, q]
        change pullback.lift (pullback.fst (gA a) O.ι ≫ (V₀ a.1 a.2).ι)
          (pullback.snd (gA a) O.ι) ?_ ≫
            pullback.snd (pullback.snd g U.toBase) O.ι = _
        exact pullback.lift_snd _ _ _
  have hkclosed (a : A) : IsClosedImmersion (k a ≫ pullback.snd f Unew.toBase) := by
    rw [hcomp]
    refine (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
      (morphismRestrictOpensRange (gA a) O.ι)).mp ?_
    exact IsZariskiLocalAtTarget.restrict_of_le (by simpa using iInf_le Oa a) (hclosed a)
  -- The point of `pullback (gA a) O.ι` above the chosen point `v a.1 a.2`, and the fact that it
  -- is the only point of that pullback over the distinguished point.
  have hcondpt (a : A) (z : ↥(pullback (gA a) O.ι)) :
      gA a (pullback.fst (gA a) O.ι z) = O.ι (pullback.snd (gA a) O.ι z) := by
    exact hom_apply_congr (pullback.condition (f := gA a) (g := O.ι)) z
  have hz (a : A) : ∃ z : ↥(pullback (gA a) O.ι),
      pullback.fst (gA a) O.ι z = v a.1 a.2 ∧ pullback.snd (gA a) O.ι z = Unew.point := by
    obtain ⟨-, -, -, hva, -, -⟩ := hfinite a.1 a.2
    let zpre : (gA a) ⁻¹ᵁ O := ⟨v a.1 a.2, by
      change gA a (v a.1 a.2) ∈ (O : Set U.scheme)
      rw [hva]
      exact hO⟩
    let z : ↥(pullback (gA a) O.ι) := (pullbackRestrictIsoRestrict (gA a) O).inv zpre
    have hfst : pullback.fst (gA a) O.ι z = v a.1 a.2 := by
      change ((pullbackRestrictIsoRestrict (gA a) O).inv ≫ pullback.fst (gA a) O.ι) zpre = _
      rw [pullbackRestrictIsoRestrict_inv_fst]
      rfl
    refine ⟨z, hfst, Subtype.ext ?_⟩
    change O.ι (pullback.snd (gA a) O.ι z) = U.point
    rw [← hcondpt a z, hfst, hva]
  have hchosen (a : A) (z : ↥(pullback (gA a) O.ι))
      (hzbase : pullback.snd f Unew.toBase (k a z) = Unew.point) :
      pullback.fst (gA a) O.ι z = v a.1 a.2 := by
    have hsnd : pullback.snd (gA a) O.ι z = Unew.point :=
      (hom_apply_congr (hcomp a) z).symm.trans hzbase
    have hcond := hcondpt a z
    rw [hsnd] at hcond
    obtain ⟨-, hfiber, -, -, -, -⟩ := hfinite a.1 a.2
    have hm : pullback.fst (gA a) O.ι z ∈ gA a ⁻¹' {U.point} := hcond
    rw [hfiber] at hm
    exact Set.mem_singleton_iff.mp hm
  -- The compatibilities of the comparison maps with the two projections.
  have hk₀fst (a : A) :
      k₀ a ≫ pullback.fst q O.ι = pullback.fst (gA a) O.ι ≫ (V₀ a.1 a.2).ι := by
    dsimp [k₀, pullback.map]
    simp only [pullback.lift_fst]
  have hk₀v (a : A) (z : ↥(pullback (gA a) O.ι)) (hz : pullback.fst (gA a) O.ι z = v a.1 a.2) :
      pullback.fst q O.ι (k₀ a z) = (V₀ a.1 a.2).ι (v a.1 a.2) := by
    rw [← hz]
    exact hom_apply_congr (hk₀fst a) z
  have hj₂eq : j₂ = eMid.inv ≫ pullback.fst q O.ι := by
    apply pullback.hom_ext
    · dsimp [j₂, pullback.map]
      rw [pullback.lift_fst, Category.comp_id, Category.assoc,
        ← pullbackLeftPullbackSndIso_inv_fst g U.toBase O.ι]
    · dsimp [j₂, pullback.map]
      rw [pullback.lift_snd]
      change pullback.snd g Unew.toBase ≫ O.ι =
        eMid.inv ≫ pullback.fst q O.ι ≫ pullback.snd g U.toBase
      calc
        pullback.snd g Unew.toBase ≫ O.ι = (eMid.inv ≫ pullback.snd q O.ι) ≫ O.ι := by
          rw [← pullbackLeftPullbackSndIso_inv_snd_snd g U.toBase O.ι]
        _ = eMid.inv ≫ pullback.fst q O.ι ≫ pullback.snd g U.toBase := by
          have hcond : pullback.fst q O.ι ≫ pullback.snd g U.toBase =
              pullback.snd q O.ι ≫ O.ι := by
            simpa [q] using (pullback.condition (f := q) (g := O.ι))
          simpa [Category.assoc] using congrArg (fun t => eMid.inv ≫ t) hcond.symm
  have hj₀fst : j₀ ≫ pullback.fst f Unew.toBase = pullback.fst g Unew.toBase ≫ W.ι := by
    dsimp [j₀]
    calc
      eW.inv ≫ pullback.snd W.ι (pullback.fst f Unew.toBase) ≫ pullback.fst f Unew.toBase =
          eW.inv ≫ pullback.fst W.ι (pullback.fst f Unew.toBase) ≫ W.ι := by
        have hcond := pullback.condition (f := W.ι) (g := pullback.fst f Unew.toBase)
        simpa [Category.assoc] using congrArg (fun t => eW.inv ≫ t) hcond.symm
      _ = pullback.fst g Unew.toBase ≫ W.ι := by
        rw [← Category.assoc, pullbackRightPullbackFstIso_inv_fst f Unew.toBase W.ι]
  have hj₀snd : j₀ ≫ pullback.snd f Unew.toBase = pullback.snd g Unew.toBase := by
    dsimp [j₀]
    rw [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd f Unew.toBase W.ι]
  refine ⟨Unew, m, V, fun a => ⟨?_, ?_⟩, ?_, ?_⟩
  · have e' : Arrow.mk ((k a).opensRange.ι ≫ pullback.snd f Unew.toBase) ≅
        Arrow.mk (k a ≫ pullback.snd f Unew.toBase) :=
      Arrow.isoMk (asIso (k a).isoOpensRange.inv) (Iso.refl _) (by simp)
    exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion) e').mpr (hkclosed a)
  · obtain ⟨z, -, hsnd⟩ := hz a
    refine ⟨k a z, ⟨z, rfl⟩, ?_⟩
    exact (hom_apply_congr (hcomp a) z).trans hsnd
  · intro a b hab y hay hby hybase
    change y ∈ Set.range (k a) at hay
    obtain ⟨za, rfl⟩ := hay
    change k a za ∈ Set.range (k b) at hby
    obtain ⟨zb, hzb⟩ := hby
    refine hab (hinjective ?_)
    calc
      (V₀ a.1 a.2).ι (v a.1 a.2) = pullback.fst q O.ι (k₀ a za) :=
        (hk₀v a za (hchosen a za hybase)).symm
      _ = pullback.fst q O.ι (k₀ b zb) :=
        congrArg _ (eMid.hom.isOpenEmbedding.injective (j₀.isOpenEmbedding.injective hzb.symm))
      _ = (V₀ b.1 b.2).ι (v b.1 b.2) := hk₀v b zb (hchosen b zb (by rwa [hzb]))
  · intro i y hybase hyx
    have hyW : y ∈ (pullback.fst f Unew.toBase) ⁻¹ᵁ W := by
      change pullback.fst f Unew.toBase y ∈ (W : Set X)
      rw [hyx]
      exact hW i
    have hyQ : y ∈ Set.range (pullback.snd W.ι (pullback.fst f Unew.toBase)) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      simpa using hyW
    obtain ⟨zQ, hzQ⟩ := hyQ
    let ynew : Pnew := eW.hom zQ
    have hyj₀ : j₀ ynew = y := by
      change (eW.inv ≫ pullback.snd W.ι (pullback.fst f Unew.toBase)) (eW.hom zQ) = y
      simpa [Scheme.Hom.comp_apply] using hzQ
    have hnewbase : pullback.snd g Unew.toBase ynew = Unew.point := by
      rw [← hyj₀] at hybase
      exact (hom_apply_congr hj₀snd ynew).symm.trans hybase
    have hnewfst : pullback.fst g Unew.toBase ynew = x' i := by
      apply Subtype.ext
      rw [← hyj₀] at hyx
      exact (hom_apply_congr hj₀fst ynew).symm.trans hyx
    have hJ₂point : j₂ ynew = pullback.fst q O.ι (eMid.inv ynew) := hom_apply_congr hj₂eq ynew
    have hmidBase : pullback.snd q O.ι (eMid.inv ynew) = Unew.point := by
      exact (hom_apply_congr (pullbackLeftPullbackSndIso_inv_snd_snd g U.toBase O.ι) ynew).trans
        hnewbase
    have hOldbase : pullback.snd g U.toBase (j₂ ynew) = U.point := by
      rw [hJ₂point]
      exact (hom_apply_congr (pullback.condition (f := q) (g := O.ι)) (eMid.inv ynew)).trans
        (congrArg O.ι hmidBase)
    have hOldfst : pullback.fst g U.toBase (j₂ ynew) = x' i := by
      rw [hJ₂point]
      exact (hom_apply_congr (pullbackLeftPullbackSndIso_inv_fst g U.toBase O.ι) ynew).trans
        hnewfst
    obtain ⟨j, hj⟩ := hcover i (j₂ ynew) hOldbase hOldfst
    obtain ⟨z, hfst, -⟩ := hz ⟨i, j⟩
    have hmidEq : k₀ ⟨i, j⟩ z = eMid.inv ynew := by
      apply (pullback.fst q O.ι).isOpenEmbedding.injective
      calc
        pullback.fst q O.ι (k₀ ⟨i, j⟩ z) = (V₀ i j).ι (v i j) := hk₀v ⟨i, j⟩ z hfst
        _ = j₂ ynew := hj
        _ = pullback.fst q O.ι (eMid.inv ynew) := hJ₂point
    refine ⟨j, z, ?_⟩
    calc
      k ⟨i, j⟩ z = j₀ (eMid.hom (k₀ ⟨i, j⟩ z)) := rfl
      _ = j₀ ynew := by
        rw [hmidEq]
        simp
      _ = y := hyj₀

end AlgebraicGeometry

end
