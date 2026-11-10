module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Noetherian.Retrocompact
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProper
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.DenseOpen
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrum
public import StacksFrontier.RingTheory.LocalCohomology.Deps.PuncturedSpectrumAffine

/-!
# Finite étale covers over a dense open with closed complement

Let `X` be a scheme and `U ⊆ X` a dense open subscheme whose inclusion is quasi-compact, and
suppose that every point of `X ∖ U` is closed and that the punctured spectrum of every strict
henselization of its local ring is connected. Then a morphism between finite étale covers of
`X` is determined by, and can be recovered from, its restriction to `U`: the base-change
functor `FÉt_X ⥤ FÉt_U` is fully faithful.

Faithfulness needs only the density of `U`. Fullness is local on the source of the first cover,
because two morphisms into a finite étale cover which agree on a dominant subscheme are equal.
Near a point lying over `x ∈ X ∖ U`, the local scheme `Spec 𝒪_{X,x}` meets `U` exactly in the
punctured spectrum of `𝒪_{X,x}`, where the connectedness hypothesis makes restriction of finite
étale covers fully faithful.

## Main results

* `AlgebraicGeometry.fullyFaithful_finiteEtaleBaseChange_of_quasiCompact_of_isClosed_compl` —
  **Stacks Tag 0BSA**: restriction of finite étale covers to a dense, quasi-compactly embedded
  open whose complement consists of closed points with connected punctured strict local
  spectra is fully faithful.
* `AlgebraicGeometry.preimage_fromSpecStalk_eq_puncturedSpectrum` — at a point outside an open
  whose outside points are all closed, the local scheme meets the open exactly in the punctured
  spectrum of the local ring.
* `AlgebraicGeometry.exists_hom_of_openCover_of_isDominant` — a morphism into a finite étale
  cover which is given locally on an open cover of the base, compatibly with a prescribed
  morphism from a dominant subscheme, glues.

## Implementation notes

The dense open subscheme is presented as an open immersion `j : U ⟶ X` which is dominant. For
an open immersion, `IsDominant j` says that `Set.range j.base` is dense, and `Set.range j.base`
is the underlying set of the open subscheme `j.opensRange`; so `IsDominant j` is precisely the
statement that the open `U` is dense in `X`. Likewise retrocompactness of that open — the
condition appearing in the source — is recorded as `QuasiCompact j`: the preimage under `j` of
a quasi-compact open `V` is quasi-compact and `j` is a homeomorphism onto its image, which
meets `V` in that image, so the open is retrocompact.

The local extensions are glued over an open cover of the source of the cover rather than by
induction on the complement, so no finiteness assumption on the complement is needed.

## References

* [Stacks Project, Tag 0BSA](https://stacks.math.columbia.edu/tag/0BSA)
* [Stacks Project, Tag 0BQE](https://stacks.math.columbia.edu/tag/0BQE)
* [Stacks Project, Tag 0BLQ](https://stacks.math.columbia.edu/tag/0BLQ)
* [Stacks Project, Tag 0BQ5](https://stacks.math.columbia.edu/tag/0BQ5)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing
open Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- The first projection of a base change, computed on a morphism of schemes over the base. -/
private alias over_pullback_map_left_fst := GlueingNearPoint.over_pullback_map_fst

/-- The second projection of a base change is unchanged by a morphism of schemes over the
base. -/
private lemma over_pullback_map_left_snd {C : Type*} [Category C] [HasPullbacks C]
    {B T : C} (p : T ⟶ B) {X Y : Over B} (f : X ⟶ Y) :
    ((Over.pullback p).map f).left ≫ pullback.snd Y.hom p = pullback.snd X.hom p := by
  simp [Over.pullback]

/-- A morphism over the base is sent by base change to `f` as soon as it is compatible with `f`
on the first projections. -/
private lemma over_pullback_map_eq_of_fst {S T : Scheme.{u}} (j : T ⟶ S) {A B : Over S}
    (g : A ⟶ B) (f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B)
    (h : f.left ≫ pullback.fst B.hom j = pullback.fst A.hom j ≫ g.left) :
    (Over.pullback j).map g = f := by
  ext1
  apply pullback.hom_ext
  · rw [over_pullback_map_left_fst, h]
  · rw [over_pullback_map_left_snd]
    simpa only [Over.pullback_obj_hom] using f.w.symm

/-- At a point `x` outside an open `U` all of whose outside points are closed, the local scheme
`Spec 𝒪_{X,x}` meets `U` exactly in the punctured spectrum of `𝒪_{X,x}`. -/
public lemma preimage_fromSpecStalk_eq_puncturedSpectrum
    {X : Scheme.{u}} (U : X.Opens) (x : X) (hx : x ∉ U)
    (hclosed : ∀ y : X, y ∉ U → IsClosed ({y} : Set X)) :
    (X.fromSpecStalk x) ⁻¹ᵁ U = puncturedSpectrum (X.presheaf.stalk x) := by
  ext p
  constructor
  · intro hp hpc
    subst p
    change X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x)) ∈ U at hp
    exact hx (by simpa only [Scheme.fromSpecStalk_closedPoint] using hp)
  · intro hp
    by_contra hy
    have hs : X.fromSpecStalk x p ⤳ x := by
      have hm : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hm
    have hpx : x = X.fromSpecStalk x p := hs.mem_closed (hclosed _ hy) rfl
    refine hp ((X.fromSpecStalk x).isEmbedding.injective ?_)
    simpa only [Scheme.fromSpecStalk_closedPoint] using hpx.symm

/-- The pullback of a dominant morphism along an open map is dominant. -/
private theorem isDominant_pullback_snd_of_isOpenMap
    {D X V : Scheme.{u}} (d : D ⟶ X) [IsDominant d]
    (i : V ⟶ X) (hi : IsOpenMap i) : IsDominant (pullback.snd d i) := by
  constructor
  change Dense (Set.range (pullback.snd d i))
  rw [Scheme.Pullback.range_snd]
  exact d.denseRange.preimage hi

/-- **Local extensions over a dominant subscheme glue.** Let `q : Y ⟶ S` be finite étale, let
`d : D ⟶ X` be dominant, let `f : D ⟶ Y` be a morphism, and suppose that on each member of an
open cover of `X` a morphism to `Y` over `S` is given which agrees with `f` on the pullback of
`d`. Then these morphisms glue to a single morphism `X ⟶ Y` over `S` restricting to `f`. -/
public theorem exists_hom_of_openCover_of_isDominant
    {D X Y S : Scheme.{u}} (d : D ⟶ X) [IsDominant d]
    (p : X ⟶ S) (q : Y ⟶ S) [IsFinite q] [Etale q]
    (f : D ⟶ Y)
    (𝒰 : X.OpenCover) (g : ∀ i, 𝒰.X i ⟶ Y)
    (hg : ∀ i, g i ≫ q = 𝒰.f i ≫ p)
    (he : ∀ i, pullback.fst d (𝒰.f i) ≫ f = pullback.snd d (𝒰.f i) ≫ g i) :
    ∃ h : X ⟶ Y, h ≫ q = p ∧ d ≫ h = f := by
  have hgg (i j : 𝒰.I₀) :
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ g j := by
    let a := pullback.fst (𝒰.f i) (𝒰.f j)
    let b := pullback.snd (𝒰.f i) (𝒰.f j)
    let c := a ≫ 𝒰.f i
    have hc : c = b ≫ 𝒰.f j := pullback.condition
    have : IsDominant (pullback.snd d c) :=
      isDominant_pullback_snd_of_isOpenMap d c c.isOpenEmbedding.isOpenMap
    refine eq_of_isDominant_of_finiteEtale q
      (by simpa only [c, a, b, Category.assoc, hg] using congrArg (fun k => k ≫ p) hc)
      (pullback.snd d c) ?_
    let li : pullback d c ⟶ pullback d (𝒰.f i) :=
      pullback.lift (pullback.fst d c) (pullback.snd d c ≫ a)
        (by simpa [c, Category.assoc] using (pullback.condition (f := d) (g := c)))
    let lj : pullback d c ⟶ pullback d (𝒰.f j) :=
      pullback.lift (pullback.fst d c) (pullback.snd d c ≫ b)
        (by rw [Category.assoc, ← hc]; exact pullback.condition)
    have hi := congrArg (fun k => li ≫ k) (he i)
    have hj := congrArg (fun k => lj ≫ k) (he j)
    simp only [li, lj, pullback.lift_fst_assoc, pullback.lift_snd_assoc] at hi hj
    simpa only [Category.assoc] using hi.symm.trans hj
  let h := 𝒰.glueMorphisms g hgg
  refine ⟨h, 𝒰.hom_ext _ _ fun i ↦ by simp [h, hg], ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ d) _ _ fun i ↦ ?_
  change pullback.fst d (𝒰.f i) ≫ (d ≫ h) = pullback.fst d (𝒰.f i) ≫ f
  rw [pullback.condition_assoc, show 𝒰.f i ≫ h = g i from 𝒰.ι_glueMorphisms g hgg i]
  exact (he i).symm

/-- **Extension of a morphism near a point of the complement.** Let `V` be a retrocompact open
of `X`, let `A` and `B` be finite étale over `X`, and let `f` be a morphism of their
restrictions to `V`. At a point `y` of `A` for which the trace of `V` on the local scheme of
its image is the punctured spectrum with connected strict henselizations, the
morphism `f` extends over an open neighbourhood of `y`, compatibly with `f` on the pullback
of `V`. -/
private theorem exists_openImmersion_extension_of_notMem
    (X : Scheme.{u}) (V : X.Opens) (hV : IsRetrocompact (V : Set X))
    (A B : Over X) (hA : IsFinite A.hom ∧ Etale A.hom)
    (hB : IsFinite B.hom ∧ Etale B.hom)
    (f : (Over.pullback V.ι).obj A ⟶ (Over.pullback V.ι).obj B)
    (y : A.left)
    (hpunct : (X.fromSpecStalk (A.hom y)) ⁻¹ᵁ V =
      puncturedSpectrum (X.presheaf.stalk (A.hom y)))
    (hconn : IsConnectedPuncturedStrictHenselization (X.presheaf.stalk (A.hom y))) :
    ∃ (W : Scheme.{u}) (i : W ⟶ A.left) (_ : IsOpenImmersion i) (g : W ⟶ B.left),
      g ≫ B.hom = i ≫ A.hom ∧ y ∈ Set.range i ∧
      pullback.fst (pullback.fst A.hom V.ι) i ≫ f.left ≫ pullback.fst B.hom V.ι =
        pullback.snd (pullback.fst A.hom V.ι) i ≫ g := by
  let Y : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ A.hom hA
  let Z : FiniteEtaleOver X := MorphismProperty.Over.mk ⊤ B.hom hB
  let fV : (finiteEtaleBaseChange V.ι).obj Y ⟶ (finiteEtaleBaseChange V.ι).obj Z :=
    MorphismProperty.Over.homMk f.left f.w
  obtain ⟨W, hVW, hxW, t, htZ, hext⟩ :=
    exists_opens_extension_of_connected_puncturedSpectrum V hV (A.hom y) hpunct hconn Y Z fV
  let t' : pullback A.hom W.ι ⟶ B.left := t
  have htZ' : t' ≫ B.hom = pullback.snd A.hom W.ι ≫ W.ι := htZ
  have hext' : openPullbackMap A.hom hVW ≫ t' = f.left ≫ pullback.fst B.hom V.ι := hext
  have hcond : pullback.fst A.hom W.ι ≫ A.hom = pullback.snd A.hom W.ι ≫ W.ι :=
    pullback.condition
  have hmi : openPullbackMap A.hom hVW ≫ pullback.fst A.hom W.ι =
      pullback.fst A.hom V.ι := openPullbackMap_fst A.hom hVW
  have hkey : pullback.fst (pullback.fst A.hom V.ι) (pullback.fst A.hom W.ι) ≫
      openPullbackMap A.hom hVW =
      pullback.snd (pullback.fst A.hom V.ι) (pullback.fst A.hom W.ι) := by
    apply (cancel_mono (pullback.fst A.hom W.ι)).mp
    rw [Category.assoc, hmi]
    exact pullback.condition
  refine ⟨pullback A.hom W.ι, pullback.fst A.hom W.ι, inferInstance, t',
    htZ'.trans hcond.symm, ?_, ?_⟩
  · rw [Scheme.Pullback.range_fst]
    exact ⟨⟨A.hom y, hxW⟩, rfl⟩
  · rw [← hext', ← Category.assoc, hkey]

/-- **Fullness of restriction to a dense retrocompact open.** Let `V` be a dense retrocompact
open of `X` all of whose outside points have, as local scheme, a punctured spectrum with
connected strict henselizations. Then every morphism of the restrictions to `V` of two finite
étale covers of `X` is the restriction of a morphism over `X`. -/
@[sga "1 XIII 4.7" "partial"]
private theorem exists_extension_of_local_full
    (X : Scheme.{u}) (V : X.Opens) [IsDominant V.ι]
    (hV : IsRetrocompact (V : Set X))
    (hpunct : ∀ x : X, x ∉ V →
      (X.fromSpecStalk x) ⁻¹ᵁ V = puncturedSpectrum (X.presheaf.stalk x))
    (hconn : ∀ x : X, x ∉ V → IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x))
    (A B : Over X) (hA : IsFinite A.hom ∧ Etale A.hom)
    (hB : IsFinite B.hom ∧ Etale B.hom)
    (f : (Over.pullback V.ι).obj A ⟶ (Over.pullback V.ι).obj B) :
    ∃ g : A ⟶ B, (Over.pullback V.ι).map g = f := by
  classical
  have : IsFinite A.hom := hA.1
  have : Etale A.hom := hA.2
  have : IsFinite B.hom := hB.1
  have : Etale B.hom := hB.2
  let D := pullback A.hom V.ι
  let d : D ⟶ A.left := pullback.fst A.hom V.ι
  let f₀ : D ⟶ B.left := f.left ≫ pullback.fst B.hom V.ι
  have hf₀ : f₀ ≫ B.hom = d ≫ A.hom := by
    simp only [f₀, Category.assoc, pullback.condition]
    have fw : f.left ≫ pullback.snd B.hom V.ι = pullback.snd A.hom V.ι := f.w
    rw [← Category.assoc, fw]
    exact pullback.condition.symm
  have : IsDominant d := by
    constructor
    change Dense (Set.range (pullback.fst A.hom V.ι))
    rw [Scheme.Pullback.range_fst]
    exact V.ι.denseRange.preimage A.hom.isOpenMap
  have hex (y : A.left) : ∃ (W : Scheme.{u}) (i : W ⟶ A.left)
      (_ : IsOpenImmersion i) (g : W ⟶ B.left),
      g ≫ B.hom = i ≫ A.hom ∧ y ∈ Set.range i ∧
      pullback.fst d i ≫ f₀ = pullback.snd d i ≫ g := by
    by_cases hy : A.hom y ∈ V
    · refine ⟨D, d, inferInstance, f₀, hf₀, ?_, ?_⟩
      · change y ∈ Set.range (pullback.fst A.hom V.ι)
        rw [Scheme.Pullback.range_fst]
        exact ⟨⟨A.hom y, hy⟩, rfl⟩
      · rw [(cancel_mono d).mp (pullback.condition (f := d) (g := d))]
    · exact exists_openImmersion_extension_of_notMem X V hV A B hA hB f y
        (hpunct _ hy) (hconn _ hy)
  choose W i hi g hg hy he using hex
  have (y : A.left) : IsOpenImmersion (i y) := hi y
  let 𝒰 : A.left.OpenCover := {
    I₀ := A.left
    X := W
    f := i
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun y => ⟨y, hy y⟩, inferInstance⟩ }
  obtain ⟨g₀, hg₀, hdg⟩ := exists_hom_of_openCover_of_isDominant d A.hom B.hom f₀ 𝒰 g hg he
  exact ⟨Over.homMk g₀ hg₀, over_pullback_map_eq_of_fst _ _ f hdg.symm⟩

/-- Along an isomorphism, every morphism of base changes is the base change of a morphism over
the original base. -/
private theorem exists_overHom_of_isIso
    {S T : Scheme.{u}} (j : T ⟶ S) [IsIso j] (A B : Over S)
    (f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B) :
    ∃ g : A ⟶ B, (Over.pullback j).map g = f := by
  let g : A ⟶ B := Over.homMk
    (inv (pullback.fst A.hom j) ≫ f.left ≫ pullback.fst B.hom j) (by
      rw [Category.assoc, Category.assoc, pullback.condition]
      have fw : f.left ≫ pullback.snd B.hom j = pullback.snd A.hom j := f.w
      rw [← Category.assoc f.left, fw, ← pullback.condition]
      simp)
  exact ⟨g, over_pullback_map_eq_of_fst _ _ f (by simp [g])⟩

/-- **Fullness of restriction along a dense quasi-compact open immersion.** Let `j : T ⟶ S` be
a dominant quasi-compact open immersion all of whose outside points have, as local scheme, a
punctured spectrum with connected strict henselizations. Then every morphism of the base changes
along `j` of two finite étale covers of `S` is the base change of a morphism over `S`. -/
private theorem exists_extension_of_openImmersion_local_full
    {S T : Scheme.{u}} (j : T ⟶ S) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j]
    (hpunct : ∀ x : S, x ∉ j.opensRange →
      (S.fromSpecStalk x) ⁻¹ᵁ j.opensRange = puncturedSpectrum (S.presheaf.stalk x))
    (hconn : ∀ x : S, x ∉ j.opensRange →
      IsConnectedPuncturedStrictHenselization (S.presheaf.stalk x))
    (A B : Over S) (hA : IsFinite A.hom ∧ Etale A.hom)
    (hB : IsFinite B.hom ∧ Etale B.hom)
    (f : (Over.pullback j).obj A ⟶ (Over.pullback j).obj B) :
    ∃ g : A ⟶ B, (Over.pullback j).map g = f := by
  let V := j.opensRange
  have hV : IsRetrocompact (V : Set S) := by
    intro O hOc hOo
    have hc := (QuasiCompact.isCompact_preimage (f := j) O hOo hOc).image j.continuous
    change IsCompact (Set.range j ∩ O)
    simpa only [Set.image_preimage_eq_range_inter] using hc
  have : IsDominant V.ι := ⟨by
    change Dense (Set.range V.ι)
    rw [Scheme.Opens.range_ι]
    exact j.denseRange⟩
  let e := j.isoOpensRange
  have hj : j = e.hom ≫ V.ι := j.isoOpensRange_hom_ι.symm
  let α : Over.pullback j ≅ Over.pullback V.ι ⋙ Over.pullback e.hom :=
    eqToIso (congrArg (fun k : T ⟶ S => Over.pullback k) hj) ≪≫
      Over.pullbackComp e.hom V.ι
  let f' := (α.app A).inv ≫ f ≫ (α.app B).hom
  obtain ⟨fV, hfV⟩ := exists_overHom_of_isIso e.hom
    ((Over.pullback V.ι).obj A) ((Over.pullback V.ι).obj B) f'
  obtain ⟨g, hg⟩ := exists_extension_of_local_full S V hV hpunct hconn A B hA hB fV
  refine ⟨g, ?_⟩
  apply (cancel_mono (α.app B).hom).mp
  calc
    _ = (α.app A).hom ≫ (Over.pullback e.hom).map ((Over.pullback V.ι).map g) :=
      α.hom.naturality g
    _ = _ := by rw [hg, hfV]; simp [f']

/-- Let `j : U ⟶ X` be a dense open immersion of schemes which is quasi-compact, and assume that
every point of `X ∖ U` is closed and that the punctured spectrum of every strict henselization of
its local ring is connected. Then restriction of finite étale covers along `j` is fully
faithful. -/
@[stacks 0BSA]
public theorem fullyFaithful_finiteEtaleBaseChange_of_quasiCompact_of_isClosed_compl
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [IsDominant j]
    [QuasiCompact j]
    (hclosed : ∀ x : X, x ∉ Set.range j.base → IsClosed ({x} : Set X))
    (hconnected : ∀ x : X, x ∉ Set.range j.base →
      IsConnectedPuncturedStrictHenselization (X.presheaf.stalk x)) :
    Nonempty (finiteEtaleBaseChange j).FullyFaithful := by
  classical
  let F := finiteEtaleBaseChange j
  have : F.Faithful := faithful_finiteEtaleBaseChange_of_isDominant j
  have : F.Full := ⟨fun {A B} f => by
    obtain ⟨g, hg⟩ := exists_extension_of_openImmersion_local_full j
      (fun x hx => preimage_fromSpecStalk_eq_puncturedSpectrum j.opensRange x hx hclosed)
      hconnected
      (Over.mk A.hom) (Over.mk B.hom) A.prop B.prop f.hom
    refine ⟨MorphismProperty.Over.homMk g.left g.w, ?_⟩
    ext1
    exact congrArg Over.Hom.left hg⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful F⟩

end AlgebraicGeometry

end
