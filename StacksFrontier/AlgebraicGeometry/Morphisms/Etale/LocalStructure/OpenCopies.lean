module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.Order.CompleteLattice.SetLike
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.TopologicalProperties.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.EtaleLocalStructure.ClosedImmersionOpens

/-!
# Étale local structure of a morphism étale at finitely many points

Let `f : X ⟶ S` be a morphism of schemes which is étale at finitely many distinct points
`x₁, …, xₙ` of a single fibre `f ⁻¹' {s}`. Passing to a suitable étale neighbourhood `(U, u)`
of `(S, s)` separates those points: the base change `X ×_S U` contains finitely many open
subschemes `V_{i,j}`, each mapping isomorphically onto `U`, no two of which meet over `u`, and
every point of the fibre of `X ×_S U` over `u` lying above some `xᵢ` belongs to one of them.

This is the étale analogue of the corresponding statement for unramified morphisms, where the
open subschemes are only closed immersions over the base: an étale closed immersion is an open
immersion, so the closed immersions produced there become isomorphisms once the base is shrunk
to the intersection of their images.

## Main definitions

* `AlgebraicGeometry.EtaleNeighborhood.restrict` restricts an étale neighbourhood to an open
  subset of its underlying scheme containing the distinguished point.

## Main results

* `AlgebraicGeometry.exists_open_etale_of_etaleAt`: a morphism étale at a point is étale over an
  open neighbourhood of that point.
* `AlgebraicGeometry.IsZariskiLocalAtSource.comp_iSup_ι`: a property of morphisms local at the
  source passes from the restrictions to a family of opens to the restriction to their supremum.
* `AlgebraicGeometry.exists_etaleNeighborhood_openCopies_cover_fibers`: the étale neighbourhood
  and the open copies of it inside the base change.

## Implementation notes

The base change is Mathlib's `CategoryTheory.Limits.pullback f U.toBase`, and the open copies are
indexed by dependent pairs `⟨i, j⟩` with `i : Fin n` and `j : Fin (m i)`. The condition that two
distinct copies do not meet over the distinguished point is stated directly on points of an
intersection; the covering condition is stated through the two canonical projections of the
pullback.

Shrinking the base to the intersection of the images of the copies is carried out with
`AlgebraicGeometry.EtaleNeighborhood.restrict`, and the copies are transported along the two
pullback pasting isomorphisms `CategoryTheory.Limits.pullbackLeftPullbackSndIso` and
`CategoryTheory.Limits.pullbackRightPullbackFstIso`.

## References

* [Stacks Project, Tag 04HL](https://stacks.math.columbia.edu/tag/04HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

/-- The restriction of an étale neighbourhood of `(S, s)` to an open subset of its underlying
scheme containing the distinguished point. It is again an étale neighbourhood of `(S, s)`,
because an open immersion is étale. -/
public def EtaleNeighborhood.restrict {S : Scheme.{u}} {s : S} (U : EtaleNeighborhood S s)
    (Q : U.scheme.Opens) (hQ : U.point ∈ Q) : EtaleNeighborhood S s :=
  U.comp (EtaleNeighborhood.ofEtale Q.ι ⟨U.point, hQ⟩)

/-- The scheme underlying a restricted étale neighbourhood is the open subscheme. -/
@[simp]
public lemma EtaleNeighborhood.restrict_scheme {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (Q : U.scheme.Opens) (hQ : U.point ∈ Q) :
    (U.restrict Q hQ).scheme = Q.toScheme := rfl

/-- The distinguished point of a restricted étale neighbourhood is the original one. -/
@[simp]
public lemma EtaleNeighborhood.restrict_point {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (Q : U.scheme.Opens) (hQ : U.point ∈ Q) :
    (U.restrict Q hQ).point = ⟨U.point, hQ⟩ := rfl

/-- The structure morphism of a restricted étale neighbourhood is the original one, precomposed
with the inclusion of the open subscheme. -/
@[simp]
public lemma EtaleNeighborhood.restrict_toBase {S : Scheme.{u}} {s : S}
    (U : EtaleNeighborhood S s) (Q : U.scheme.Opens) (hQ : U.point ∈ Q) :
    (U.restrict Q hQ).toBase = Q.ι ≫ U.toBase := rfl

/-- A property of morphisms of schemes which is Zariski local at the source holds for the
restriction of a morphism to a supremum of open sets as soon as it holds for the restriction to
each of them. -/
public lemma IsZariskiLocalAtSource.comp_iSup_ι {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ i, P ((U i).ι ≫ f)) : P ((⨆ i, U i).ι ≫ f) := by
  set W : X.Opens := ⨆ i, U i with hW
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := P) (f := W.ι ≫ f)
    (fun i ↦ W.ι ⁻¹ᵁ U i) ?_ fun i ↦ ?_
  · refine le_antisymm le_top fun y _ ↦ ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp y.2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · have hrange : Set.range ((W.ι ⁻¹ᵁ U i).ι ≫ W.ι) = Set.range (U i).ι := by
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      show W.ι '' (W.ι ⁻¹' (U i : Set X)) = (U i : Set X)
      rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
      exact Set.inter_eq_left.mpr (le_iSup U i)
    have hfac : (IsOpenImmersion.isoOfRangeEq ((W.ι ⁻¹ᵁ U i).ι ≫ W.ι) (U i).ι hrange).hom ≫
        (U i).ι = (W.ι ⁻¹ᵁ U i).ι ≫ W.ι := by simp
    rw [← Category.assoc, ← hfac, Category.assoc, P.cancel_left_of_respectsIso]
    exact hU i

/-- A morphism of schemes which is étale at a point is étale over an open neighbourhood of that
point: there is an open set containing the point whose inclusion, followed by the morphism, is
étale. -/
public lemma exists_open_etale_of_etaleAt {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (hx : EtaleAt f x) : ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨U, hU, hxU, V, hV, hUV, hEt⟩ := hx
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : Etale (f.resLE V U hUV) :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).2
      ((RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U hUV)).2 hEt)
  refine ⟨U, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι f hUV]
  infer_instance

/-- **Stacks Project, Tag 04HL.** A morphism which is étale at finitely many distinct points of
one fibre admits, after an étale base change, open subschemes of the base change which map
isomorphically onto the new base, meet one another nowhere over the distinguished point, and
together contain every point of that fibre lying over one of the given points. -/
@[stacks 04HL]
public theorem exists_etaleNeighborhood_openCopies_cover_fibers
    {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) (x : Fin n → X) (s : S)
    (hinj : Function.Injective x) (hx : ∀ i, f (x i) = s) (hetale : ∀ i, EtaleAt f (x i)) :
    ∃ (U : EtaleNeighborhood S s) (m : Fin n → ℕ)
      (V : (Σ i, Fin (m i)) → (pullback f U.toBase).Opens),
      (∀ a, IsIso ((V a).ι ≫ pullback.snd f U.toBase)) ∧
      (∀ a b, a ≠ b → ∀ z : (pullback f U.toBase : Scheme.{u}),
        z ∈ (V a).1 → z ∈ (V b).1 → pullback.snd f U.toBase z ≠ U.point) ∧
      (∀ i (z : (pullback f U.toBase : Scheme.{u})),
        pullback.snd f U.toBase z = U.point → pullback.fst f U.toBase z = x i →
          ∃ j : Fin (m i), z ∈ (V ⟨i, j⟩).1) := by
  choose U₀ hxU₀ hU₀et using fun i ↦ exists_open_etale_of_etaleAt f (hetale i)
  let W : X.Opens := ⨆ i, U₀ i
  have : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale)
  have hW : Etale (W.ι ≫ f) := IsZariskiLocalAtSource.comp_iSup_ι (P := @Etale) f U₀ hU₀et
  let x₀ : Fin n → W.toScheme := fun i ↦
    ⟨x i, TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hxU₀ i⟩⟩
  have hinj₀ : Function.Injective x₀ := fun i j hij ↦ hinj (congrArg Subtype.val hij)
  have hunram₀ : ∀ i, UnramifiedAt (W.ι ≫ f) (x₀ i) := fun i ↦
    ((etaleAt_iff_smoothAt_and_unramifiedAt (W.ι ≫ f) (x₀ i)).mp
      ((etale_iff_forall_etaleAt (W.ι ≫ f)).mp hW (x₀ i))).2
  obtain ⟨U, m, V, hclosed, hdisjoint, hcover⟩ :=
    exists_etaleNeighborhood_isClosedImmersion_opens_of_unramifiedAt
      (W.ι ≫ f) n x₀ s hx hinj₀ hunram₀
  let q (a : Σ i, Fin (m i)) : (V a).toScheme ⟶ U.scheme :=
    (V a).ι ≫ pullback.snd (W.ι ≫ f) U.toBase
  have hqOpen (a : Σ i, Fin (m i)) : IsOpenImmersion (q a) := by
    have : IsClosedImmersion (q a) := (hclosed a).1
    infer_instance
  let I : U.scheme.Opens := ⨅ a, (q a).opensRange
  have hUI : (U.point : U.scheme) ∈ I := by
    show U.point ∈ ((⨅ a, (q a).opensRange : U.scheme.Opens) : Set U.scheme)
    rw [TopologicalSpace.Opens.coe_iInf]
    exact Set.mem_iInter.mpr fun a ↦ let ⟨y, hy, hys⟩ := (hclosed a).2; ⟨⟨y, hy⟩, hys⟩
  let u : I.toScheme := ⟨U.point, hUI⟩
  let P₀ : Scheme.{u} := pullback (W.ι ≫ f) U.toBase
  let Pbase : Scheme.{u} := pullback (pullback.snd (W.ι ≫ f) U.toBase) I.ι
  let Ebase : Pbase ≅ pullback (W.ι ≫ f) (I.ι ≫ U.toBase) :=
    pullbackLeftPullbackSndIso (W.ι ≫ f) U.toBase I.ι
  have hbase (p : Pbase)
      (hp : pullback.snd (pullback.snd (W.ι ≫ f) U.toBase) I.ι p = u) :
      pullback.snd (W.ι ≫ f) U.toBase
        (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι p) = U.point := by
    have h := congrArg (fun g ↦ g p)
      (pullback.condition (f := pullback.snd (W.ι ≫ f) U.toBase) (g := I.ι))
    rwa [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hp] at h
  let K : pullback (W.ι ≫ f) (I.ι ≫ U.toBase) ⟶ pullback f (I.ι ≫ U.toBase) :=
    pullback.map (W.ι ≫ f) (I.ι ≫ U.toBase) f (I.ι ≫ U.toBase) W.ι (𝟙 _) (𝟙 _)
      (by simp) (by simp)
  have hKsnd : K ≫ pullback.snd f (I.ι ≫ U.toBase) =
      pullback.snd (W.ι ≫ f) (I.ι ≫ U.toBase) :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hKfst : K ≫ pullback.fst f (I.ι ≫ U.toBase) =
      pullback.fst (W.ι ≫ f) (I.ι ≫ U.toBase) ≫ W.ι :=
    pullback.lift_fst _ _ _
  let L (a : Σ i, Fin (m i)) :
      pullback (V a).ι (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι) ⟶
        pullback f (I.ι ≫ U.toBase) :=
    pullback.snd (V a).ι (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι) ≫ Ebase.hom ≫ K
  let Ecopy (a : Σ i, Fin (m i)) :=
    pullbackRightPullbackFstIso (pullback.snd (W.ι ≫ f) U.toBase) I.ι (V a).ι
  have hLopen (a : Σ i, Fin (m i)) : IsOpenImmersion (L a) := by
    dsimp only [L]
    infer_instance
  have hqIso (a : Σ i, Fin (m i)) : IsIso (pullback.snd (q a) I.ι) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine TopologicalSpace.Opens.ext (Set.eq_univ_iff_forall.mpr fun y ↦ ?_)
    exact (iInf_le (fun a ↦ (q a).opensRange) a) y.2
  have hLbase (a : Σ i, Fin (m i)) :
      L a ≫ pullback.snd f (I.ι ≫ U.toBase) =
        (Ecopy a).hom ≫ pullback.snd (q a) I.ι := by
    dsimp only [L, Ecopy, q, Ebase]
    rw [Category.assoc, Category.assoc, hKsnd, pullbackLeftPullbackSndIso_hom_snd,
      pullbackRightPullbackFstIso_hom_snd]
  have hLiso (a : Σ i, Fin (m i)) :
      IsIso (L a ≫ pullback.snd f (I.ι ≫ U.toBase)) := by
    rw [hLbase]
    have := hqIso a
    infer_instance
  let V' (a : Σ i, Fin (m i)) : (pullback f (I.ι ≫ U.toBase)).Opens := (L a).opensRange
  have hcopy (a : Σ i, Fin (m i)) :
      IsIso ((V' a).ι ≫ pullback.snd f (I.ι ≫ U.toBase)) := by
    have hfac : (L a).isoOpensRange.hom ≫ (V' a).ι = L a := by simp [V']
    rw [← isIso_comp_left_iff (L a).isoOpensRange.hom, ← Category.assoc, hfac]
    exact hLiso a
  have hrange (c : Σ i, Fin (m i)) (p : Pbase) :
      p ∈ Set.range (pullback.snd (V c).ι
        (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι)) ↔
        pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι p ∈ V c := by
    rw [IsOpenImmersion.range_pullbackSnd]
    simp
  have hsep (a b : Σ i, Fin (m i)) (hab : a ≠ b)
      (z : (pullback f (I.ι ≫ U.toBase) : Scheme.{u}))
      (hza : z ∈ (V' a).1) (hzb : z ∈ (V' b).1) :
      pullback.snd f (I.ι ≫ U.toBase) z ≠ u := by
    intro hz
    obtain ⟨ya, hya⟩ := (Scheme.Hom.mem_opensRange (f := L a)).mp (by simpa [V'] using hza)
    obtain ⟨yb, hyb⟩ := (Scheme.Hom.mem_opensRange (f := L b)).mp (by simpa [V'] using hzb)
    let pa : Pbase := pullback.snd (V a).ι
      (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι) ya
    let pb : Pbase := pullback.snd (V b).ι
      (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι) yb
    have hpa : pa = pb := by
      have hK : K (Ebase.hom pa) = K (Ebase.hom pb) := by
        simpa [L, pa, pb] using hya.trans hyb.symm
      simpa using congrArg Ebase.inv (K.isOpenEmbedding.injective hK)
    let y : P₀ := pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι pa
    have hyA : y ∈ V a := (hrange a pa).1 ⟨ya, rfl⟩
    have hyB : y ∈ V b := by
      have := (hrange b pb).1 ⟨yb, rfl⟩
      rwa [← hpa] at this
    refine hdisjoint a b hab y hyA hyB ?_
    have hpoint : pullback.snd (q a) I.ι ((Ecopy a).hom ya) = u := by
      have h := congrArg (pullback.snd f (I.ι ≫ U.toBase)) hya
      rw [← Scheme.Hom.comp_apply, hLbase a] at h
      exact h.trans hz
    refine hbase pa ?_
    have h := congrArg (fun g ↦ g ya)
      (pullbackRightPullbackFstIso_hom_snd (pullback.snd (W.ι ≫ f) U.toBase) I.ι (V a).ι)
    simpa [Ecopy, pa, Pbase, Scheme.Hom.comp_apply] using h.symm.trans hpoint
  have hcov (i : Fin n) (z : (pullback f (I.ι ≫ U.toBase) : Scheme.{u}))
      (hzU : pullback.snd f (I.ι ≫ U.toBase) z = u)
      (hzX : pullback.fst f (I.ι ≫ U.toBase) z = x i) :
      ∃ j : Fin (m i), z ∈ (V' ⟨i, j⟩).1 := by
    have hzK : z ∈ Set.range K := by
      dsimp only [K]
      rw [Scheme.Pullback.range_map]
      exact ⟨⟨x₀ i, by simpa [x₀] using hzX.symm⟩, ⟨u, by simpa using hzU.symm⟩⟩
    obtain ⟨p₁, hp₁⟩ := hzK
    have hp₁U : pullback.snd (W.ι ≫ f) (I.ι ≫ U.toBase) p₁ = u := by
      have h := congrArg (pullback.snd f (I.ι ≫ U.toBase)) hp₁
      rw [← Scheme.Hom.comp_apply, hKsnd] at h
      exact h.trans hzU
    let pbase : Pbase := Ebase.inv p₁
    have hEb : Ebase.hom pbase = p₁ := by simp [pbase]
    let y : P₀ := pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι pbase
    have hybase : pullback.snd (W.ι ≫ f) U.toBase y = U.point := by
      refine hbase pbase ?_
      have h := congrArg (fun g ↦ g pbase)
        (pullbackLeftPullbackSndIso_hom_snd (W.ι ≫ f) U.toBase I.ι)
      have h' := congrArg (pullback.snd (W.ι ≫ f) (I.ι ≫ U.toBase)) hEb
      rw [← Scheme.Hom.comp_apply, h] at h'
      simpa [Pbase] using h'.trans hp₁U
    have hyx : pullback.fst (W.ι ≫ f) U.toBase y = x₀ i := by
      refine W.ι.isOpenEmbedding.injective ?_
      have h := congrArg (pullback.fst f (I.ι ≫ U.toBase)) hp₁
      rw [← Scheme.Hom.comp_apply, hKfst] at h
      have h' := congrArg (fun g ↦ g pbase)
        (pullbackLeftPullbackSndIso_hom_fst (W.ι ≫ f) U.toBase I.ι)
      have h'' := congrArg (pullback.fst (W.ι ≫ f) (I.ι ≫ U.toBase)) hEb
      rw [← Scheme.Hom.comp_apply, h'] at h''
      calc W.ι (pullback.fst (W.ι ≫ f) U.toBase y)
          = (pullback.fst (W.ι ≫ f) (I.ι ≫ U.toBase) ≫ W.ι) p₁ := by
            simpa [y, Pbase, Scheme.Hom.comp_apply] using congrArg W.ι h''
        _ = pullback.fst f (I.ι ≫ U.toBase) z := h
        _ = x i := hzX
    obtain ⟨j, hyV⟩ := hcover i y hybase hyx
    refine ⟨j, ?_⟩
    obtain ⟨w, hw⟩ := (hrange ⟨i, j⟩ pbase).2 hyV
    show z ∈ Set.range (L ⟨i, j⟩)
    refine ⟨w, ?_⟩
    show K (Ebase.hom (pullback.snd (V ⟨i, j⟩).ι
      (pullback.fst (pullback.snd (W.ι ≫ f) U.toBase) I.ι) w)) = z
    rw [hw, hEb]
    exact hp₁
  exact ⟨U.restrict I hUI, m, V', hcopy, hsep, hcov⟩

end AlgebraicGeometry

end
