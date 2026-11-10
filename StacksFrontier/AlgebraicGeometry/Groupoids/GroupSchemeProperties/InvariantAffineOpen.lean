module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.Norm.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.FlatGroupoid
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.BaseChange
public import StacksFrontier.RingTheory.Ideal.FinitePrimeAvoidance

/-!
# Invariant affine neighbourhoods in a finite locally free groupoid scheme

Let a groupoid scheme have finite locally free source and target maps.  If the orbit of a point
of the object scheme is contained in an affine open, then that point has an invariant affine
open neighbourhood.

The proof shrinks the given affine open twice.  First the orbit, which is finite, is put inside
a basic open of the affine open still contained in the complement of the image of the arrows
leaving that affine open; this uses prime avoidance in the ring of the affine open.  Then the
norm along the target map of the corresponding section is taken: the locus where that norm is
invertible is affine, and it is invariant because the norm is nonzero at a point exactly when
the section is nonzero at every point of the fibre above it.

## Main results

* `AlgebraicGeometry.GroupoidScheme.exists_invariant_affine_open_of_orbit_subset_affine`: the
  invariant affine open neighbourhood.

## Implementation notes

That the orbit of `x` lies in an affine open is written pointwise: every arrow with source `x`
has its target in that open.  `Stacks.Groupoids.IsInvariantOpen` is the invariant-open predicate
and `Stacks.Norm.MorphismNormMap` the kind of norm used; for a finite locally free morphism
the norm taken is `Stacks.Divisors.finiteLocallyFreeNorm`.

`Stacks.Groupoids.GroupoidScheme.equivalence_sourceTargetRel` is recorded here because the fact
that a groupoid scheme cuts out an equivalence relation on points is currently re-derived inline
wherever it is used.

## References

* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TopologicalSpace

universe u

namespace Stacks.Groupoids.GroupoidScheme

/-- The relation on points of the object scheme of a groupoid scheme cut out by its source and
target maps is an equivalence relation. -/
theorem equivalence_sourceTargetRel {S : Scheme.{u}} (G : GroupoidScheme S) :
    Equivalence (Function.SourceTargetRel G.source.left.base G.target.left.base) := by
  simpa [AlgebraicGeometry.groupoidPreRelation, PreRelation.target, PreRelation.source] using
    AlgebraicGeometry.PreRelation.equivalence_sourceTargetRel
      (AlgebraicGeometry.groupoidPreRelation G)
      (AlgebraicGeometry.groupoidPreRelation_isPreEquivalenceRelation G)

/-- The source of an identity arrow is its base point. -/
private theorem source_identity_base {S : Scheme.{u}} (G : GroupoidScheme S)
    (y : G.objects.left) :
    G.source.left.base (G.identity.left.base y) = y := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun f : G.objects ⟶ G.objects => f.left.base y) G.source_identity

/-- The target of an identity arrow is its base point. -/
private theorem target_identity_base {S : Scheme.{u}} (G : GroupoidScheme S)
    (y : G.objects.left) :
    G.target.left.base (G.identity.left.base y) = y := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun f : G.objects ⟶ G.objects => f.left.base y) G.target_identity

/-- Alias of `AlgebraicGeometry.GroupoidScheme.source_inverse_apply`. -/
private alias source_inverse_base := AlgebraicGeometry.GroupoidScheme.source_inverse_apply

/-- The target of the inverse of an arrow is the source of that arrow. -/
private theorem target_inverse_base {S : Scheme.{u}} (G : GroupoidScheme S)
    (r : G.arrows.left) :
    G.target.left.base (G.inverse.left.base r) = G.source.left.base r := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun f : G.arrows ⟶ G.objects => f.left.base r) G.target_inverse

end Stacks.Groupoids.GroupoidScheme

namespace AlgebraicGeometry

/-- A global section of an affine scheme whose basic open is the whole space is a unit. -/
theorem isUnit_of_basicOpen_eq_top {X : Scheme.{u}} [IsAffine X] (s : Γ(X, ⊤))
    (hs : X.basicOpen s = ⊤) : IsUnit s := by
  have hs' : PrimeSpectrum.basicOpen s = ⊤ := by
    have h := congrArg (fun V : X.Opens => (isAffineOpen_top X).fromSpec ⁻¹ᵁ V) hs
    rwa [(isAffineOpen_top X).fromSpec_preimage_basicOpen,
      (isAffineOpen_top X).fromSpec_preimage_self] at h
  refine Ideal.span_singleton_eq_top.mp ?_
  have hcov : (⨆ _ : Unit, PrimeSpectrum.basicOpen s) = ⊤ := by simpa using hs'
  simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff (ι := Unit) (f := fun _ => s)).mp hcov

/-- A finite subset of an open subset of an affine scheme lies in a basic open which is still
contained in that open subset. -/
theorem exists_basicOpen_of_finite_subset {X : Scheme.{u}} [IsAffine X] {K : Set X}
    (hK : K.Finite) (V : X.Opens) (hKV : K ⊆ V) :
    ∃ r : Γ(X, ⊤), K ⊆ X.basicOpen r ∧ X.basicOpen r ≤ V := by
  classical
  choose f₀ hle₀ hmem₀ using fun x (hx : x ∈ K) =>
    (isAffineOpen_top X).exists_basicOpen_le ⟨x, hKV hx⟩ (by simp)
  let F : X → Γ(X, ⊤) := fun x => if hx : x ∈ K then f₀ x hx else 0
  let I : Ideal Γ(X, ⊤) := Ideal.span (F '' K)
  let P : X → Ideal Γ(X, ⊤) := fun x => RingHom.ker (X.evaluation ⊤ x (by simp)).hom
  obtain ⟨r, hrI, hrAvoid⟩ :=
    exists_mem_forall_notMem_of_forall_not_le (I := I) (hK.image P)
      (by rintro q ⟨x, -, rfl⟩; exact RingHom.ker_isPrime _)
      (by
        rintro q ⟨x, hxK, rfl⟩ hsub
        have hmem : F x ∈ I := Ideal.subset_span ⟨x, hxK, rfl⟩
        refine absurd ((RingHom.mem_ker).mp (hsub hmem)) ?_
        simpa [F, hxK] using
          (X.evaluation_ne_zero_iff_mem_basicOpen x (by simp) (f₀ x hxK)).mpr (hmem₀ x hxK))
  refine ⟨r, fun y hyK => ?_, fun y hyD => ?_⟩
  · refine (X.evaluation_ne_zero_iff_mem_basicOpen y (by simp) r).mp fun hzero => ?_
    exact hrAvoid (P y) ⟨y, hyK, rfl⟩ ((RingHom.mem_ker).mpr hzero)
  · by_contra hyV
    have hIker : I ≤ P y := by
      refine Ideal.span_le.2 ?_
      rintro g ⟨z, hzK, rfl⟩
      refine (RingHom.mem_ker).mpr
        ((X.evaluation_eq_zero_iff_notMem_basicOpen y (by simp) (F z)).mpr fun hyFz => ?_)
      exact hyV (hle₀ z hzK (by simpa [F, hzK] using hyFz))
    exact ((X.evaluation_ne_zero_iff_mem_basicOpen y (by simp) r).mpr hyD)
      ((RingHom.mem_ker).mpr (hIker hrI))

/-- A section over an affine open whose basic open is that whole open is a unit. -/
private theorem isUnit_of_le_basicOpen {X : Scheme.{u}} (A : X.Opens) [IsAffine A.toScheme]
    (s : Γ(X, A)) (hs : A ≤ X.basicOpen s) : IsUnit s := by
  have hbasic : A.toScheme.basicOpen (A.topIso.inv s) = ⊤ := by
    refine le_antisymm le_top fun z _ => ?_
    have : A.ι z ∈ A.ι ''ᵁ A.toScheme.basicOpen (A.topIso.inv s) := by
      rw [A.ι_image_basicOpen_topIso_inv]
      exact hs z.2
    rwa [Scheme.Hom.apply_mem_image_iff] at this
  exact (MulEquiv.isUnit_map A.topIso.commRingCatIsoToRingEquiv.symm (x := s)).mp
    (isUnit_of_basicOpen_eq_top _ hbasic)

/-- A section pulled back along a morphism is nonzero at a point exactly when the section is
nonzero at the image of that point. -/
theorem evaluation_appTop_ne_zero_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) (x : X) :
    X.evaluation ⊤ x (by simp) ((ConcreteCategory.hom (Scheme.Hom.app f ⊤)) s) ≠ 0 ↔
      Y.evaluation ⊤ (f x) (by simp) s ≠ 0 := by
  have hEval : (f.residueFieldMap x).hom (Y.evaluation ⊤ (f x) (by simp) s) =
      X.evaluation ⊤ x (by simp) ((ConcreteCategory.hom (Scheme.Hom.app f ⊤)) s) :=
    Scheme.evaluation_naturality_apply f x (by simp) s
  rw [← hEval]
  exact map_ne_zero _

/-- A global section of an open subscheme pulled back along a morphism is nonzero at a point
exactly when the image of that point lies in the image of the basic open of the section. -/
private theorem evaluation_appTop_ne_zero_iff_mem_image {X Z : Scheme.{u}} (W : X.Opens)
    (g : Z ⟶ W.toScheme) (f : Γ(W.toScheme, ⊤)) (b : Z) :
    Z.evaluation ⊤ b (by simp) ((ConcreteCategory.hom (Scheme.Hom.app g ⊤)) f) ≠ 0 ↔
      W.ι (g b) ∈ W.ι ''ᵁ W.toScheme.basicOpen f := by
  refine (evaluation_appTop_ne_zero_iff g f b).trans <|
    (W.toScheme.evaluation_ne_zero_iff_mem_basicOpen (g b) (by simp) f).trans
      (Scheme.Hom.apply_mem_image_iff W.ι).symm

/-- A section over an open is nonzero at a point of that open exactly when the point lies in the
basic open of the section restricted to the open subscheme. -/
private theorem evaluation_ι_ne_zero_iff {X : Scheme.{u}} (T : X.Opens) (s : Γ(X, T))
    (z : T.toScheme) :
    X.evaluation T (T.ι z) z.2 s ≠ 0 ↔ z ∈ T.toScheme.basicOpen (T.ι.app T s) := by
  have hEval : (T.ι.residueFieldMap z).hom (X.evaluation T (T.ι z) z.2 s) =
      T.toScheme.evaluation (T.ι ⁻¹ᵁ T) z z.2 (T.ι.app T s) :=
    Scheme.evaluation_naturality_apply T.ι z z.2 s
  rw [← T.toScheme.evaluation_ne_zero_iff_mem_basicOpen z z.2 (T.ι.app T s), ← hEval]
  exact (map_ne_zero _).symm

/-- For a finite morphism carrying a norm, the norm of a section is nonzero at a point of the
target exactly when the section is nonzero at every point of the fibre over it. -/
theorem norm_evaluation_ne_zero_iff {X Y : Scheme.{u}} (p : X ⟶ Y) [IsFinite p]
    (N : Stacks.Norm.MorphismNormMap p) (U : Y.Opens) (s : Γ(X, p ⁻¹ᵁ U)) (y : Y)
    (hy : y ∈ U) :
    Y.evaluation U y hy (N.app U s) ≠ 0 ↔
      ∀ (x : X) (hxy : p x = y),
        X.evaluation (p ⁻¹ᵁ U) x (by change p x ∈ U; rw [hxy]; exact hy) s ≠ 0 := by
  refine ⟨fun h x hxy hzero => ?_, fun h => ?_⟩
  · subst y
    exact h (N.app_eq_zero_at_image s x (by simpa using hy) hzero)
  · classical
    let T : X.Opens := p ⁻¹ᵁ U
    let q := p ∣_ U
    let C : Set T.toScheme := (T.toScheme.basicOpen (T.ι.app T s) : Set T.toScheme)ᶜ
    have hclosed : IsClosed (q.base '' C) :=
      q.isClosedMap C (T.toScheme.basicOpen (T.ι.app T s)).2.isClosed_compl
    let O0 : U.toScheme.Opens := ⟨(q.base '' C)ᶜ, hclosed.isOpen_compl⟩
    let O : Y.Opens := U.ι ''ᵁ O0
    have hyO : y ∈ O := by
      change ∃ z : U.toScheme, z ∈ O0 ∧ U.ι z = y
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      simp only [O0]
      rintro ⟨z, hzC, hzq⟩
      have hxy : p.base z.1 = y := by
        simpa [q, Scheme.Hom.comp_apply] using congrArg Subtype.val hzq
      exact absurd ((evaluation_ι_ne_zero_iff T s z).mp (h (T.ι z) hxy)) hzC
    obtain ⟨_, ⟨V, hVaff, rfl⟩, hyV, hVO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyO O.2
    have hVle : V ≤ U := by
      intro z hz
      obtain ⟨w, -, rfl⟩ := hVO hz
      exact w.2
    let i : V ⟶ U := homOfLE hVle
    let sV : Γ(X, p ⁻¹ᵁ V) := X.presheaf.map ((Opens.map p.base).map i).op s
    have hAT : p ⁻¹ᵁ V ≤ T := fun _ hz => hVle hz
    have hUnit : IsUnit sV := by
      have : IsAffine (p ⁻¹ᵁ V).toScheme := (show IsAffineOpen V from hVaff).preimage p
      refine isUnit_of_le_basicOpen (p ⁻¹ᵁ V) (X.presheaf.map (homOfLE hAT).op s) fun z hz => ?_
      rw [Scheme.basicOpen_res]
      refine ⟨hz, ?_⟩
      let zT : T.toScheme := ⟨z, hAT hz⟩
      obtain ⟨w, hw, heq⟩ := (hVO hz : p.base z ∈ O)
      have hqeq : q.base zT = w := U.ι.injective <|
        (show U.ι (q.base zT) = p.base z from morphismRestrict_base_coe p U zT).trans heq.symm
      have hqO : q.base zT ∈ O0 := hqeq ▸ hw
      have hzT : zT ∈ T.toScheme.basicOpen (T.ι.app T s) := by
        by_contra hzC
        exact hqO ⟨zT, by simpa [C] using hzC, rfl⟩
      simpa [zT] using (X.evaluation_ne_zero_iff_mem_basicOpen (T.ι zT) zT.2 s).mp
        ((evaluation_ι_ne_zero_iff T s zT).mpr hzT)
    have hEvalV : Y.evaluation V y hyV (N.app V sV) = Y.evaluation U y hy (N.app U s) := by
      rw [N.naturality i s]
      simp [Scheme.evaluation]
    exact hEvalV ▸ ((hUnit.map (N.app V)).map (Y.evaluation V y hyV).hom).ne_zero

namespace GroupoidScheme

open Stacks.Groupoids

/-- An open which is invariant under a groupoid scheme also contains the source of every arrow
whose target it contains. -/
private theorem _root_.Stacks.Groupoids.IsInvariantOpen.source_mem {S : Scheme.{u}}
    {G : Stacks.Groupoids.GroupoidScheme S} {W : G.objects.left.Opens}
    (hW : IsInvariantOpen G W) {r : G.arrows.left} (hr : G.target.left.base r ∈ W) :
    G.source.left.base r ∈ W :=
  G.target_inverse_base r ▸ hW (G.inverse.left.base r) (G.source_inverse_base r ▸ hr)

/-- An open consisting of the points all of whose incoming arrows have their source in a fixed
open is invariant. -/
private theorem isInvariantOpen_of_forall_source_mem {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) (V U : G.objects.left.Opens)
    (hV : ∀ y, y ∈ V ↔
      ∀ b : G.arrows.left, G.target.left.base b = y → G.source.left.base b ∈ U) :
    IsInvariantOpen G V := by
  have hE := G.equivalence_sourceTargetRel
  intro r hr
  refine (hV (G.target.left.base r)).2 fun b hb => ?_
  obtain ⟨c, hcr, hcb⟩ := hE.trans (hE.symm ⟨r, rfl, rfl⟩) ⟨b, hb, rfl⟩
  rw [← hcb]
  exact (hV (G.source.left.base r)).1 hr c hcr

/-- If every arrow leaving `x` lands in an open `W`, and the target map is universally closed,
then `W` contains an invariant open which still contains the target of every such arrow. -/
private theorem exists_isInvariantOpen_le_of_orbit_subset {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [UniversallyClosed G.target.left]
    (x : G.objects.left) (W : G.objects.left.Opens)
    (hOrbit : ∀ r : G.arrows.left, G.source.left.base r = x → G.target.left.base r ∈ W) :
    ∃ W' : G.objects.left.Opens, W' ≤ W ∧ IsInvariantOpen G W' ∧
      ∀ r : G.arrows.left, G.source.left.base r = x → G.target.left.base r ∈ W' := by
  have hE := G.equivalence_sourceTargetRel
  let C : Set G.arrows.left := G.source.left.base ⁻¹' (W : Set G.objects.left)ᶜ
  have hC : IsClosed (G.target.left.base '' C) :=
    G.target.left.isClosedMap C (W.2.isClosed_compl.preimage (by fun_prop))
  refine ⟨⟨(G.target.left.base '' C)ᶜ, hC.isOpen_compl⟩, fun y hy => ?_, fun r hr => ?_,
    fun r hr => ?_⟩
  · by_contra hyW
    exact hy ⟨G.identity.left.base y,
      by simpa [C, Stacks.Groupoids.GroupoidScheme.source_identity_base] using hyW,
      G.target_identity_base y⟩
  · rintro ⟨s, hsC, hst⟩
    obtain ⟨t, htt, hty⟩ := hE.trans (hE.symm ⟨r, rfl, rfl⟩) ⟨s, hst, rfl⟩
    exact hr ⟨t, by simpa [C, hty] using hsC, htt⟩
  · rintro ⟨s, hsC, hsr⟩
    obtain ⟨t, hts, htx⟩ := hE.trans (hE.symm ⟨s, hsr, rfl⟩) ⟨r, rfl, hr⟩
    exact hsC (hts ▸ hOrbit t htx)

/-- In a groupoid scheme with finite locally free target map, let `f` be a function on an affine
open `W` such that every arrow whose target lies in the basic open of `f` has its source in `W`.
Then the points all of whose incoming arrows have their source in that basic open form an
affine open. -/
private theorem exists_affineOpen_forall_source_mem {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S) [Stacks.Morphisms.IsFiniteLocallyFree G.target.left]
    (W : G.objects.left.Opens) (hWaff : IsAffineOpen W) (f : Γ(W.toScheme, ⊤))
    (hsource : ∀ r : G.arrows.left,
      G.target.left.base r ∈ W.ι ''ᵁ W.toScheme.basicOpen f → G.source.left.base r ∈ W) :
    ∃ V : G.objects.left.Opens, IsAffineOpen V ∧ ∀ y, y ∈ V ↔
      ∀ b : G.arrows.left, G.target.left.base b = y →
        G.source.left.base b ∈ W.ι ''ᵁ W.toScheme.basicOpen f := by
  let U : G.objects.left.Opens := W.ι ''ᵁ W.toScheme.basicOpen f
  have : IsAffine W.toScheme := hWaff
  have hUaff : IsAffineOpen U :=
    ((isAffineOpen_top W.toScheme).basicOpen f).image_of_isOpenImmersion W.ι
  have : IsAffine U.toScheme := hUaff
  let T : G.arrows.left.Opens := G.target.left ⁻¹ᵁ U
  have hTW : T ≤ G.source.left ⁻¹ᵁ W := fun r hr => hsource r hr
  let g : T.toScheme ⟶ W.toScheme := G.arrows.left.homOfLE hTW ≫ (G.source.left ∣_ W)
  have hgcomp : g ≫ W.ι = T.ι ≫ G.source.left := by
    dsimp [g]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, G.arrows.left.homOfLE_ι hTW]
  have hgbase (a : T.toScheme) : W.ι (g a) = G.source.left.base (T.ι a) :=
    congrArg (fun f : T.toScheme ⟶ G.objects.left => f a) hgcomp
  let q : T.toScheme ⟶ U.toScheme := G.target.left ∣_ U
  have : Stacks.Morphisms.IsFiniteLocallyFree q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict G.target.left U).flip inferInstance
  have : IsFinite q := Stacks.Morphisms.IsFiniteLocallyFree.isFinite q
  let s : Γ(T.toScheme, ⊤) := g.appTop.hom f
  let N : Stacks.Norm.MorphismNormMap q :=
    (Stacks.Divisors.finiteLocallyFreeNorm q).toMorphismNormMap
  let n : Γ(U.toScheme, ⊤) := N.app ⊤ s
  have hqbase (b : T.toScheme) : (q b).1 = G.target.left.base (T.ι b) :=
    morphismRestrict_base_coe G.target.left U b
  have hkey (b : T.toScheme) :
      T.toScheme.evaluation ⊤ b (by simp) s ≠ 0 ↔ G.source.left.base (T.ι b) ∈ U := by
    rw [← hgbase b]
    exact evaluation_appTop_ne_zero_iff_mem_image W g f b
  refine ⟨U.ι ''ᵁ U.toScheme.basicOpen n,
    ((isAffineOpen_top U.toScheme).basicOpen n).image_of_isOpenImmersion U.ι, fun y => ⟨?_, ?_⟩⟩
  · rintro ⟨yu, hyn, rfl⟩ b hb
    have hbT : G.target.left.base b ∈ U := by
      rw [hb]
      exact yu.2
    have hq : q ⟨b, hbT⟩ = yu := Subtype.ext ((hqbase _).trans (hb.trans (U.ι_apply yu)))
    exact (hkey _).1 ((norm_evaluation_ne_zero_iff q N ⊤ s yu (by simp)).1
      ((U.toScheme.evaluation_ne_zero_iff_mem_basicOpen yu (by simp) n).2 hyn) _ hq)
  · intro hy
    have hyU : y ∈ U := by
      simpa only [Stacks.Groupoids.GroupoidScheme.source_identity_base] using
        hy _ (G.target_identity_base y)
    let yu : U.toScheme := ⟨y, hyU⟩
    refine ⟨yu, (U.toScheme.evaluation_ne_zero_iff_mem_basicOpen yu (by simp) n).1 ?_, rfl⟩
    exact (norm_evaluation_ne_zero_iff q N ⊤ s yu (by simp)).2 fun b hb =>
      (hkey b).2 (hy _ ((hqbase b).symm.trans (congrArg Subtype.val hb)))

/-- **Stacks Project, Tag 03JE.** In a groupoid scheme with finite locally free source and
target maps, a point whose orbit is contained in an affine open has an invariant affine open
neighbourhood. -/
@[stacks 03JE, sga "1 V 1.8" "orbit⊂affine⇒inv affine"]
theorem exists_invariant_affine_open_of_orbit_subset_affine {S : Scheme.{u}}
    (G : Stacks.Groupoids.GroupoidScheme S)
    [Stacks.Morphisms.IsFiniteLocallyFree G.source.left]
    [Stacks.Morphisms.IsFiniteLocallyFree G.target.left] (x : G.objects.left)
    (h : ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
      ∀ r : G.arrows.left, G.source.left.base r = x → G.target.left.base r ∈ W) :
    ∃ V : G.objects.left.Opens, IsAffineOpen V ∧ x ∈ V ∧ IsInvariantOpen G V := by
  classical
  obtain ⟨W, hWaff, hOrbit⟩ := h
  have : IsFinite G.source.left := Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
  have : IsFinite G.target.left := Stacks.Morphisms.IsFiniteLocallyFree.isFinite _
  let K : Set G.objects.left := G.target.left.base '' (G.source.left.base ⁻¹' {x})
  have hKfinite : K.Finite :=
    (G.source.left.finite_preimage_singleton x).image G.target.left.base
  obtain ⟨W', hW'le, hW'inv, hW'orbit⟩ := exists_isInvariantOpen_le_of_orbit_subset G x W hOrbit
  have hKW' : K ⊆ W' := Set.image_subset_iff.2 fun r hr => hW'orbit r hr
  have : IsAffine W.toScheme := hWaff
  let Kaff : Set W.toScheme := fun y => y.1 ∈ K
  obtain ⟨f, hKf, hfW⟩ := exists_basicOpen_of_finite_subset
    (Set.Finite.preimage (Set.injOn_of_injective Subtype.val_injective) hKfinite : Kaff.Finite)
    (W.ι ⁻¹ᵁ W') fun y hy => hKW' hy
  have hKU : K ⊆ W.ι ''ᵁ W.toScheme.basicOpen f := by
    rintro y ⟨r, hrA, rfl⟩
    exact ⟨⟨G.target.left.base r, hW'le (hKW' ⟨r, hrA, rfl⟩)⟩, hKf ⟨r, hrA, rfl⟩, rfl⟩
  have hUW' : W.ι ''ᵁ W.toScheme.basicOpen f ≤ W' := by
    rintro y ⟨z, hz, rfl⟩
    exact hfW hz
  obtain ⟨V, hVaff, hV⟩ := exists_affineOpen_forall_source_mem G W hWaff f fun r hr =>
    hW'le (IsInvariantOpen.source_mem hW'inv (r := r) (hUW' hr))
  refine ⟨V, hVaff, (hV x).2 fun b hb => ?_, isInvariantOpen_of_forall_source_mem G V _ hV⟩
  obtain ⟨r, hrb, hrx⟩ := G.equivalence_sourceTargetRel.symm ⟨b, hb, rfl⟩
  exact hKU ⟨r, hrx, hrb⟩

end GroupoidScheme

end AlgebraicGeometry

end
