module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings

/-!
# Recognising V coverings by refinement

A family of morphisms of schemes with a fixed target is a V covering exactly when some V
covering refines it, and exactly when the single morphism from the disjoint union of its
sources is a V covering. So the property only depends on the family up to refinement, and can
always be tested on one morphism.

## Main results

* `AlgebraicGeometry.isVCovering_tfae` — the three equivalent descriptions.
* `AlgebraicGeometry.isAffine_of_isClopen` — an open-and-closed subscheme of an affine scheme
  is affine. This is used here to cut a standard V covering of an affine into the pieces lying
  over the individual members of the family, and is stated for any consumer.

## Implementation notes

Refinement is a `CategoryTheory.PreZeroHypercover.Hom`, and the disjoint-union morphism is
`CategoryTheory.Limits.Sigma.desc` regarded as a family indexed by `Unit`. The index type is
assumed small relative to the universe of the schemes, so that the coproduct exists.

The substantial implication is that the disjoint union being a V covering forces the family
to be one. Over an affine open the standard V covering refining the disjoint union must be
cut into the pieces lying over the individual members: each source of the standard covering
decomposes into the clopen preimages of the components of the coproduct, those preimages are
again affine, only finitely many of them are nonempty because the source is quasi-compact,
and a valuation ring mapping in lands in a single one because the spectrum of a valuation
ring is connected.

## References

* [Stacks Project, Tag 0ETI](https://stacks.math.columbia.edu/tag/0ETI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u v w u' v'

namespace AlgebraicGeometry

private lemma affine_of_clopen_open {Y : Scheme.{u}} [IsAffine Y] (U : Y.Opens)
    (hU : IsClopen (U : Set Y)) : IsAffine U.toScheme := by
  let e := Y.isoSpec
  let V := e.inv ⁻¹ᵁ U
  have hV : IsClopen (V.1 : Set (PrimeSpectrum Γ(Y, ⊤))) := hU.preimage e.inv.continuous
  obtain ⟨r, -, heq⟩ := PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen hV
  have : IsAffine V.toScheme := by
    rw [show V = PrimeSpectrum.basicOpen r from TopologicalSpace.Opens.ext heq]
    exact IsAffineOpen.Spec_basicOpen r
  exact IsAffine.of_isIso (e.inv.preimageIso U).inv

/-- **An open-and-closed subscheme of an affine scheme is affine.** Transporting the
open-and-closed set to `Spec Γ(Y, ⊤)` along `AlgebraicGeometry.Scheme.isoSpec`, it becomes the
basic open of an idempotent by
`AlgebraicGeometry.PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`, and a basic open
of an affine scheme is affine. -/
public alias isAffine_of_isClopen := affine_of_clopen_open

private lemma finite_nonempty_of_compact_open_partition {Y : Type u} [TopologicalSpace Y]
    [CompactSpace Y] {I : Type v} (U : I → TopologicalSpace.Opens Y)
    (hcover : ∀ x, ∃ i, x ∈ U i)
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (U i : Set Y) (U j : Set Y)) :
    Finite {i // (U i : Set Y).Nonempty} := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set Y)) (fun i => (U i).2) (fun x _ => Set.mem_iUnion.mpr (hcover x))
  have hsub : {i | (U i : Set Y).Nonempty} ⊆ t := by
    rintro i ⟨x, hx⟩
    obtain ⟨j, hjrest⟩ := Set.mem_iUnion.mp (ht (a := x) trivial)
    obtain ⟨hjt, hxj⟩ := Set.mem_iUnion.mp hjrest
    obtain rfl : i = j := by_contra fun hne => Set.disjoint_left.mp (hdisjoint i j hne) hx hxj
    simpa using hjt
  exact (t.finite_toSet.subset hsub).to_subtype

private lemma sigma_component_isClopen {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) (i : I) :
    IsClopen ((Limits.Sigma.ι X i).opensRange : Set (∐ X : Scheme.{u})) := by
  refine ⟨isOpen_compl_iff.mp ?_, (Limits.Sigma.ι X i).opensRange.2⟩
  have hcompl : (Set.univ \ (Limits.Sigma.ι X i).opensRange : Set (∐ X : Scheme.{u})) =
      ⋃ j : {j : I // j ≠ i}, ((Limits.Sigma.ι X j.1).opensRange : Set (∐ X : Scheme.{u})) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨j, y, hy⟩ := (AlgebraicGeometry.sigmaOpenCover X).exists_eq x
      have hji : j ≠ i := by
        rintro rfl
        exact hx.2 ⟨y, hy⟩
      exact Set.mem_iUnion.mpr ⟨⟨j, hji⟩, ⟨y, hy⟩⟩
    · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact ⟨trivial, fun hi => (Set.disjoint_left.mp (TopologicalSpace.Opens.coe_disjoint.mpr
        (AlgebraicGeometry.disjoint_opensRange_sigmaι X j.1 i j.2))) hj hi⟩
  rw [Set.compl_eq_univ_sdiff, hcompl]
  exact isOpen_iUnion fun j => (Limits.Sigma.ι X j.1).opensRange.2

private lemma isClopen_preimage_sigma_component {I : Type v} [Small.{u} I]
    {Y : Scheme.{u}} (X : I → Scheme.{u}) (q : Y ⟶ ∐ X) (i : I) :
    IsClopen ((q ⁻¹ᵁ (Limits.Sigma.ι X i).opensRange : Y.Opens) : Set Y) := by
  change IsClopen (q.base ⁻¹' (Limits.Sigma.ι X i).opensRange)
  exact (sigma_component_isClopen X i).preimage q.continuous

/-- A morphism whose image lies in the range of an open immersion factors through it. -/
private lemma exists_lift_of_forall_mem {X Y Z : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : Z ⟶ Y) (h : ∀ z, g z ∈ f.opensRange) : ∃ l : Z ⟶ X, l ≫ f = g :=
  ⟨IsOpenImmersion.lift f g (by rintro _ ⟨z, rfl⟩; exact h z), IsOpenImmersion.lift_fac _ _ _⟩

private lemma connected_map_factors_through_sigma {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) {Y : Scheme.{u}} [PreconnectedSpace Y] [Nonempty Y]
    (q : Y ⟶ ∐ X) :
    ∃ (i : I) (h : Y ⟶ X i), h ≫ Limits.Sigma.ι X i = q := by
  obtain ⟨x⟩ : Nonempty Y := inferInstance
  obtain ⟨i, y, hy⟩ := (AlgebraicGeometry.sigmaOpenCover X).exists_eq (q x)
  have hwhole := (isClopen_preimage_sigma_component X q i).eq_univ ⟨x, y, hy⟩
  exact ⟨i, exists_lift_of_forall_mem _ q fun z ↦ by
    have hz : z ∈ ((q ⁻¹ᵁ (Limits.Sigma.ι X i).opensRange : Y.Opens) : Set Y) := by
      rw [hwhole]
      trivial
    exact hz⟩

private noncomputable def pullbackHom {C : Type u'} [Category.{v'} C] [HasPullbacks C]
    {T S : C}
    {E : PreZeroHypercover.{v} T} {F : PreZeroHypercover.{w} T}
    (r : E.Hom F) (g : S ⟶ T) :
  (E.pullback₂ g).Hom (F.pullback₂ g) where
  s₀ := r.s₀
  h₀ i := pullback.map (E.f i) g (F.f (r.s₀ i)) g (r.h₀ i) (𝟙 S) (𝟙 T)
    (by simpa using (r.w₀ i).symm) (by simp)
  w₀ i := by
    dsimp [PreZeroHypercover.pullback₂, pullback.map]
    simp only [Category.comp_id]
    exact pullback.lift_snd (f := F.f (r.s₀ i)) (g := g) _ _ _

/-- A family of morphisms of schemes refined by a V covering is a V covering. -/
public theorem IsVCovering.of_hom {T : Scheme.{u}} {K : Type w} {I : Type v}
    {Y : K → Scheme.{u}} {g : ∀ k, Y k ⟶ T} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hg : IsVCovering Y g)
    (r : ({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
      ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)) :
    IsVCovering X f := by
  rw [isVCovering_iff] at hg ⊢
  intro U hU
  obtain ⟨𝒱, hfinite, haffine, hstd, ⟨φ⟩⟩ := hg U hU
  exact ⟨𝒱, hfinite, haffine, hstd, ⟨φ.comp (pullbackHom r U.ι)⟩⟩

private noncomputable abbrev sigmaPiece {I : Type v} [Small.{u} I] (X : I → Scheme.{u})
    {Y : Scheme.{u}} (q : Y ⟶ ∐ X) (i : I) : Y.Opens :=
  q ⁻¹ᵁ (Sigma.ι X i).opensRange

private lemma exists_lift_sigmaPiece {I : Type v} [Small.{u} I] (X : I → Scheme.{u})
    {Y Z : Scheme.{u}} [PreconnectedSpace Z] [Nonempty Z] (q : Y ⟶ ∐ X) (h : Z ⟶ Y) :
    ∃ (i : I) (l : Z ⟶ (sigmaPiece X q i).toScheme), l ≫ (sigmaPiece X q i).ι = h := by
  obtain ⟨i, hi, hfactor⟩ := connected_map_factors_through_sigma X (h ≫ q)
  refine ⟨i, exists_lift_of_forall_mem _ h fun z ↦ ?_⟩
  rw [Scheme.Opens.opensRange_ι]
  change q (h.base z) ∈ (Sigma.ι X i).opensRange
  have heq := congrArg (fun k => k.base z) hfactor
  change (Sigma.ι X i).base (hi.base z) = q (h.base z) at heq
  exact ⟨hi.base z, heq⟩

private lemma isStandardVCovering_sigmaPieces {I : Type v} [Small.{u} I] {X : I → Scheme.{u}}
    {S : Scheme.{u}} [IsAffine S] (𝒰 : PreZeroHypercover.{u} S) [Finite 𝒰.I₀]
    [∀ j, IsAffine (𝒰.X j)] (h𝒰 : IsStandardVCovering 𝒰.X 𝒰.f) (q : ∀ j, 𝒰.X j ⟶ ∐ X)
    {J : Type u} [Finite J]
    (e : J ≃ Σ j, {i // (sigmaPiece X (q j) i : Set (𝒰.X j)).Nonempty})
    [∀ a, IsAffine (sigmaPiece X (q (e a).1) (e a).2.1).toScheme] :
    IsStandardVCovering (fun a ↦ (sigmaPiece X (q (e a).1) (e a).2.1).toScheme)
      (fun a ↦ (sigmaPiece X (q (e a).1) (e a).2.1).ι ≫ 𝒰.f (e a).1) := by
  intro V _ _ _ ξ
  obtain ⟨W, hComm, hDom, hVal, ev, hev, j, h, hξ⟩ := h𝒰 V ξ
  have : IrreducibleSpace (Spec (.of W)) := (inferInstance : IrreducibleSpace (PrimeSpectrum W))
  obtain ⟨i, l, hl⟩ := exists_lift_sigmaPiece X (q j) h
  obtain ⟨z⟩ : Nonempty (Spec (.of W)) := inferInstance
  refine ⟨W, hComm, hDom, hVal, ev, hev, e.symm ⟨j, i, (l.base z).1, (l.base z).2⟩, ?_⟩
  beta_reduce
  rw [e.apply_symm_apply]
  exact ⟨l, hξ.trans (by rw [← hl]; simp)⟩

private lemma exists_isStandardVCovering_hom_of_sigma {T : Scheme.{u}} {I : Type v}
    [Small.{u} I] {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} {S : Scheme.{u}} [IsAffine S]
    (s : S ⟶ T) (𝒰 : PreZeroHypercover.{u} S) [Finite 𝒰.I₀] [∀ j, IsAffine (𝒰.X j)]
    (h𝒰 : IsStandardVCovering 𝒰.X 𝒰.f) (q : ∀ j, 𝒰.X j ⟶ ∐ X)
    (hq : ∀ j, q j ≫ Sigma.desc f = 𝒰.f j ≫ s) :
    ∃ (𝒱 : PreZeroHypercover.{u} S) (hfinite : Finite 𝒱.I₀)
      (haffine : ∀ j, IsAffine (𝒱.X j)),
      @IsStandardVCovering S _ 𝒱.I₀ hfinite 𝒱.X haffine 𝒱.f ∧
        Nonempty (𝒱.Hom
          (({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T).pullback₂ s)) := by
  classical
  let K := Σ j, {i // (sigmaPiece X (q j) i : Set (𝒰.X j)).Nonempty}
  have hcover (j : 𝒰.I₀) (x : 𝒰.X j) : ∃ i, x ∈ sigmaPiece X (q j) i := by
    obtain ⟨i, y, hy⟩ := (AlgebraicGeometry.sigmaOpenCover X).exists_eq (q j x)
    exact ⟨i, ⟨y, hy⟩⟩
  have (j : 𝒰.I₀) : Finite {i // (sigmaPiece X (q j) i : Set (𝒰.X j)).Nonempty} :=
    finite_nonempty_of_compact_open_partition (sigmaPiece X (q j)) (hcover j)
      fun i i' hii' => Disjoint.preimage (q j).base (TopologicalSpace.Opens.coe_disjoint.mpr
        (AlgebraicGeometry.disjoint_opensRange_sigmaι X i i' hii'))
  obtain ⟨J, ⟨e⟩⟩ := Small.equiv_small.{u} (α := K)
  have : Finite J := Finite.of_equiv K e
  have (a : J) : IsAffine (sigmaPiece X (q (e.symm a).1) (e.symm a).2.1).toScheme :=
    isAffine_of_isClopen _ (isClopen_preimage_sigma_component X _ _)
  choose x hxq using fun k : K ↦ exists_lift_of_forall_mem (Sigma.ι X k.2.1)
    ((sigmaPiece X (q k.1) k.2.1).ι ≫ q k.1) fun y ↦ y.2
  have hx (k : K) : x k ≫ f k.2.1 = ((sigmaPiece X (q k.1) k.2.1).ι ≫ 𝒰.f k.1) ≫ s := by
    rw [Category.assoc, ← hq, ← Sigma.ι_comp_desc f k.2.1, ← Category.assoc, hxq, Category.assoc]
  let 𝒱 : PreZeroHypercover.{u} S :=
    { I₀ := J
      X a := (sigmaPiece X (q (e.symm a).1) (e.symm a).2.1).toScheme
      f a := (sigmaPiece X (q (e.symm a).1) (e.symm a).2.1).ι ≫ 𝒰.f (e.symm a).1 }
  exact ⟨𝒱, inferInstance, fun _ ↦ inferInstance,
    isStandardVCovering_sigmaPieces 𝒰 h𝒰 q e.symm,
    ⟨{ s₀ a := (e.symm a).2.1
       h₀ a := pullback.lift (x (e.symm a)) _ (hx (e.symm a))
       w₀ a := pullback.lift_snd _ _ _ }⟩⟩

/-- A family of morphisms of schemes is a V covering if its disjoint-union morphism is. -/
public theorem IsVCovering.of_sigmaDesc {T : Scheme.{u}} {I : Type v} [Small.{u} I]
    {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    (hf : IsVCovering (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f)) : IsVCovering X f := by
  rw [isVCovering_iff] at hf ⊢
  intro U hU
  obtain ⟨𝒰, _, _, h𝒰, ⟨φ⟩⟩ := hf U hU
  have : IsAffine U.toScheme := hU
  exact exists_isStandardVCovering_hom_of_sigma U.ι 𝒰 h𝒰
    (fun j ↦ φ.h₀ j ≫ pullback.fst (Sigma.desc f) U.ι) fun j ↦
      (Category.assoc _ _ _).trans <| (congrArg (φ.h₀ j ≫ ·) pullback.condition).trans <|
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.ι) (φ.w₀ j))

/-- A family of morphisms of schemes is a V covering if and only if a V covering refines it,
if and only if its disjoint-union morphism is a V covering. -/
@[stacks 0ETI]
public theorem isVCovering_tfae {T : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T) :
    List.TFAE [
      IsVCovering X f,
      ∃ (K : Type v) (Y : K → Scheme.{u}) (g : ∀ k, Y k ⟶ T),
        IsVCovering Y g ∧
          Nonempty
            (({ I₀ := K, X := Y, f := g } : PreZeroHypercover T).Hom
              ({ I₀ := I, X := X, f := f } : PreZeroHypercover T)),
      IsVCovering
        (fun _ : Unit ↦ ∐ X) (fun _ ↦ Sigma.desc f)] := by
  tfae_have 1 → 2 := fun hf => ⟨I, X, f, hf, ⟨.id _⟩⟩
  tfae_have 2 → 1 := fun ⟨_, _, _, hg, ⟨r⟩⟩ => hg.of_hom r
  tfae_have 1 → 3 := fun hf => hf.of_hom { s₀ _ := (), h₀ i := Sigma.ι X i }
  tfae_have 3 → 1 := IsVCovering.of_sigmaDesc
  tfae_finish

end AlgebraicGeometry
