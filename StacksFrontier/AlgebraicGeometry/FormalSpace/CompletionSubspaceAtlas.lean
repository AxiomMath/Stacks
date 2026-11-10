module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceAffineChartColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SheafifiedULiftLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Size.Monomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.CategoryTheory.Sites.Representable.LocalSurjectivityFromSiteMorphisms

/-!
# The completion of an algebraic space along a closed subspace: the atlas

Let `S` be a scheme contained in a big fppf site `B`, let `X` be an algebraic space over `S`
and let `Z ⊆ X` be a closed subspace. This file proves **Stacks 0GXY** with nothing assumed
beyond the source's hypotheses: the completion `X^∧_Z` of Stacks 0GXU is

1. locally weakly adic;
2. locally adic\* if `Z ⟶ X` is of finite presentation;
3. locally Noetherian if `X` is locally Noetherian.

The shared argument is the one of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes`: an affine étale atlas
`{W_i ⟶ X}` of `X` induces the atlas `{(W_i)^∧ ⟶ X^∧_Z}` of the completion, and over an affine
chart the completion is a completion along an ideal, whose type is Stacks 0GXX. The two inputs
those statements take as hypotheses are proved here.

* **The atlas of `X`.** Stacks 03FX,
  `AlgebraicGeometry.IsAlgebraicSpace.exists_affine_coproduct_atlas`, gives an étale surjection
  `U ⟶ X` from an object of the site with `U = ∐ W_i`, the `W_i` affine. Its summands are
  jointly locally surjective onto `X` among presheaves, and
  `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_sheafifiedULiftMap` carries that to the
  sheafified universe lifts in which the formal algebraic spaces read their coverings. The empty
  summands are discarded, so that the index injects into the points of `U`.

* **The set-theoretic condition of Stacks 0AIS for `X^∧_Z`.** The source requires it of a formal
  algebraic space. The stages `Spec (A_i ⧸ K_i ^ (n + 1))` of the chart completions are jointly
  surjective onto `X^∧_Z`; they are indexed by a set of size at most `2 ^ size U` and each has
  size at most `size U`, so their disjoint union `V` is an object of the site
  (`AlgebraicGeometry.BigFppfSite.contains_sigma_of_size_le`), and its representable sheaf is the
  coproduct of theirs (`AlgebraicGeometry.BigFppfOver.isColimitUliftYonedaSigmaCofanOfContains`).
  So `h_V ⟶ X^∧_Z` is a surjection. For the relation: `X^∧_Z ⟶ X` is a monomorphism, so the
  kernel pair of `h_V ⟶ X^∧_Z` is that of `h_V ⟶ X`, which is the algebraic space `V ×_X V`
  (Stacks 02YS), and an algebraic space receives a surjection from an object of the site.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_affine_etale_atlas_sheafifiedULift`: the affine étale
  atlas of an algebraic space, read in the universe-lifted sheaf form.
* `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSubspace`: the
  set-theoretic condition of Stacks 0AIS for `X^∧_Z`.
* `AlgebraicGeometry.FormalSpace.isLocallyWeaklyAdic_completionSubspace_of_isClosedSubspace`:
  **Stacks 0GXY (1)**.
* `AlgebraicGeometry.FormalSpace.isLocallyAdicStar_completionSubspace_of_isClosedSubspace`:
  **Stacks 0GXY (2)**.
* `AlgebraicGeometry.FormalSpace.isLocallyNoetherian_completionSubspace_of_isClosedSubspace`:
  **Stacks 0GXY (3)**.

## References

* [Stacks Project, Tag 0GXY](https://stacks.math.columbia.edu/tag/0GXY)
* [Stacks Project, Tag 0GXX](https://stacks.math.columbia.edu/tag/0GXX)
* [Stacks Project, Tag 0GXU](https://stacks.math.columbia.edu/tag/0GXU)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
* [Stacks Project, Tag 02YS](https://stacks.math.columbia.edu/tag/02YS)
* [Stacks Project, Tag 000R](https://stacks.math.columbia.edu/tag/000R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] sheaf_hasColimits

/-! ### The completion is a subsheaf of the ambient space -/

/-- The morphism `X^∧_Z ⟶ X` from the completion into the sheafified universe lift of `X` is a
monomorphism: it is the sheafification of the inclusion of a subfunctor, and sheafification
preserves kernel pairs. -/
theorem mono_completionSubspaceToAmbient (X : AlgebraicSpaces B S hS) (Z : Subfunctor X.1) :
    Mono (Space.completionSubspaceToAmbient B S hS X Z) := by
  let F := plusPlusSheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let ι := (Space.completionSubspaceSubfunctor B S hS X Z).ι
  have h : IsKernelPair (F.map ι) (F.map (𝟙 _)) (F.map (𝟙 _)) :=
    (IsKernelPair.id_of_mono ι).map F
  rw [F.map_id] at h
  exact h.mono_of_isIso_fst

/-! ### The set-theoretic condition for a subsheaf of an algebraic space -/

/-- The sheafified universe lift of an algebraic space is an algebraic space in the value
universe of the formal algebraic spaces. -/
theorem isAlgebraicSpaceULift_sheafifiedULift (X : AlgebraicSpaces B S hS) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (Space.sheafifiedULift B S hS X.1).obj := by
  have hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (X.1 ⋙ uliftFunctor.{u + 1}) := by
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_comp_uliftFunctor_iff,
      ← isSheaf_iff_isSheaf_of_type]
    exact X.2.isSheaf
  exact Space.isAlgebraicSpaceULift_of_iso B S hS
    ((BigFppfOver.topology B S hS).isoSheafify hsh)
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS X.1).mpr X.2)

/-- **The set-theoretic condition of Stacks 0AIS for a subsheaf of an algebraic space** which
receives a surjection from an object of the site. The kernel pair of `h_V ⟶ F` is the kernel
pair of `h_V ⟶ X`, `F ⟶ X` being a monomorphism; that is the algebraic space `V ×_X V` by
Stacks 02YS, and an algebraic space receives a surjection from an object of the site, its
étale scheme atlas. -/
theorem satisfiesSetTheoreticCondition_of_mono_of_epi (X : AlgebraicSpaces B S hS)
    {F : FppfSheaf B S hS} (φ : F ⟶ Space.sheafifiedULift B S hS X.1) [Mono φ]
    (V : BigFppfOver B S hS)
    (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶ F) [Epi t] :
    SatisfiesSetTheoreticCondition B S hS F := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let G := sheafToPresheaf J (Type (u + 1))
  -- the kernel pair of `t` is the kernel pair of `t ≫ φ`
  have hP : IsPullback (pullback.fst t t) (pullback.snd t t) (t ≫ φ) (t ≫ φ) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono t t φ)
  -- which is an algebraic space
  have hVa : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (J.uliftYoneda.{u + 1}.obj V).obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS (J.uliftYonedaCompSheafToPresheaf.{u + 1}.app V)
      (Space.isAlgebraicSpaceULift_uliftYoneda.{u + 1} B S hS V)
  have hPa : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback t t).obj := by
    have hpre := Space.isAlgebraicSpaceULift_pullback.{u + 1} B S hS (G.map (t ≫ φ))
      (G.map (t ≫ φ)) hVa hVa (isAlgebraicSpaceULift_sheafifiedULift B S hS X)
    exact Space.isAlgebraicSpaceULift_of_iso B S hS
      ((hP.map G).isoIsPullback _ _ (IsPullback.of_hasPullback _ _)).symm hpre
  -- an algebraic space receives a surjection from an object of the site
  obtain ⟨R, a, hsurj, hetale⟩ := hPa.exists_atlas
  have hls : Presheaf.IsLocallySurjective J a :=
    isLocallySurjective_of_surjective_etale_uliftYoneda B S hS a hsurj hetale
  refine ⟨V, R, J.uliftYoneda.{u + 1}.obj V, J.uliftYoneda.{u + 1}.obj R,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app V⟩,
    ⟨J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R⟩, t, inferInstance,
    ⟨(J.uliftYonedaCompSheafToPresheaf.{u + 1}.app R).hom ≫ a⟩, ?_⟩
  rw [← Sheaf.isLocallySurjective_iff_epi]
  exact Presheaf.isLocallySurjective_comp J _ a

/-! ### The affine étale atlas of an algebraic space -/

/-- **The affine étale atlas of an algebraic space, in the universe-lifted sheaf form.** Every
algebraic space `X` over `S` has a family of étale charts `W_i ⟶ X` by affine objects of the
site which is jointly surjective: every section of `X` lifts, locally, to one of the charts,
and consequently the sheafified universe lifts of the charts are jointly surjective. The
family comes with a bound: there is an object `U` of the site such that the index has
cardinality at most `2 ^ size U` and every chart has size at most `size U`.

The family is the one of Stacks 03FX: the nonempty summands of an étale surjection
`U = ∐ W_i ⟶ X`. -/
theorem exists_affine_etale_atlas_sheafifiedULift (X : AlgebraicSpaces B S hS) :
    ∃ (U : BigFppfOver B S hS) (I : Type u) (W : I → BigFppfOver B S hS)
      (f : ∀ i, (schemeSpaceFunctor B S hS).obj (W i) ⟶ X),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i))) ∧
      (∀ i, (Space.etaleOnSite B S hS).presheaf (f i).hom) ∧
      (∀ ⦃T : BigFppfOver B S hS⦄ (x : X.1.obj (op T)), ∃ R : Sieve T,
        R ∈ BigFppfOver.topology B S hS T ∧ ∀ ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T), R h →
          ∃ (i : I) (k : T' ⟶ W i), (f i).hom.app (op T') k = X.1.map h.op x) ∧
      Sheaf.IsLocallySurjective
        (Sigma.desc fun i : ULift.{u + 1} I ↦ Space.sheafifiedULiftMap B S hS (f i.down).hom) ∧
      #I ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj U).size ∧
      ∀ i, ((BigFppfOver.toScheme B S hS).obj (W i)).size ≤
        ((BigFppfOver.toScheme B S hS).obj U).size := by
  classical
  obtain ⟨U, f₀, I₀, W₀, j₀, e, hfS, hfE, hWaff, hje, -, hjetale, -⟩ :=
    IsAlgebraicSpace.exists_affine_coproduct_atlas B S hS X.1 X.2
  obtain ⟨hjoi, hjcov, hjdisj⟩ := isOpenImmersion_cover_disjoint_of_iso_sigma e hje
  let I : Type u := {i : I₀ // Nonempty ((BigFppfOver.toScheme B S hS).obj (W₀ i))}
  let W : I → BigFppfOver B S hS := fun i ↦ W₀ i.1
  let j : ∀ i, W i ⟶ U := fun i ↦ j₀ i.1
  let f : ∀ i, (schemeSpaceFunctor B S hS).obj (W i) ⟶ X :=
    fun i ↦ ObjectProperty.homMk (yoneda.map (j i) ≫ f₀)
  -- every section of `X` lifts locally to a summand
  have hlift : ∀ ⦃T : BigFppfOver B S hS⦄ (x : X.1.obj (op T)), ∃ R : Sieve T,
      R ∈ BigFppfOver.topology B S hS T ∧ ∀ ⦃T' : BigFppfOver B S hS⦄ (h : T' ⟶ T), R h →
        ∃ (i : I) (k : T' ⟶ W i), (f i).hom.app (op T') k = X.1.map h.op x := by
    have hf₀ : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f₀ :=
      Space.isLocallySurjective_of_surjective_etale B S hS f₀ hfS hfE
    have hcovU : Sieve.generate (Presieve.ofArrows W j) ∈ BigFppfOver.topology B S hS U := by
      refine Space.generate_ofArrows_mem_topology_of_openCover B S hS W j
        (fun i ↦ hjoi i.1) (fun x ↦ ?_)
      obtain ⟨i, y, hy⟩ := hjcov x
      exact ⟨⟨i, ⟨y⟩⟩, y, hy⟩
    intro T x
    refine Sheaf.exists_covering_of_comp (P := fun T' h ↦
      ∃ (i : I) (k : T' ⟶ W i), (f i).hom.app (op T') k = X.1.map h.op x)
      (hf₀.imageSieve_mem x) ?_
    intro T' g hg
    obtain ⟨a, ha⟩ := hg
    refine ⟨_, (BigFppfOver.topology B S hS).pullback_stable a hcovU, ?_⟩
    rintro T'' h ⟨Y, k, l, ⟨i⟩, hkl⟩
    refine ⟨i, k, ?_⟩
    change f₀.app _ (k ≫ j i) = X.1.map (h ≫ g).op x
    rw [hkl, op_comp, Functor.map_comp_apply, ← ha]
    exact NatTrans.naturality_apply f₀ h.op a
  refine ⟨U, I, W, f, fun i ↦ hWaff i.1, fun i ↦ hjetale i.1, hlift, ?_, ?_, fun i ↦ ?_⟩
  · -- joint surjectivity, first among presheaves, then after sheafifying
    apply Space.isLocallySurjective_sigmaDesc_sheafifiedULiftMap
    constructor
    intro T s
    obtain ⟨R, hR, hRl⟩ := hlift s.down
    refine (BigFppfOver.topology B S hS).superset_covering ?_ hR
    intro T' h hh
    obtain ⟨i, k, hk⟩ := hRl h hh
    let x : (((schemeSpaceFunctor B S hS).obj (W i)).1 ⋙ uliftFunctor.{u + 1}).obj (op T') :=
      ULift.up k
    refine ⟨(Sigma.ι (fun i : ULift.{u + 1} I ↦
      ((schemeSpaceFunctor B S hS).obj (W i.down)).1 ⋙ uliftFunctor.{u + 1}) ⟨i⟩).app _ x, ?_⟩
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app, Sigma.ι_comp_desc]
    exact ULift.ext hk
  · -- the nonempty summands inject into the points of `U`
    refine (Cardinal.mk_le_of_injective (f := fun i : I ↦
      ((BigFppfOver.toScheme B S hS).map (j i)).base (Classical.choice i.2)) ?_).trans
        (Scheme.mk_le_two_pow_size _)
    intro i i' hii'
    by_contra hne
    have hne' : i.1 ≠ i'.1 := fun h ↦ hne (Subtype.ext h)
    exact Set.disjoint_left.mp (hjdisj hne') ⟨_, rfl⟩ ⟨_, hii'.symm⟩
  · -- a summand is an open subscheme of `U`
    have := hjoi i.1
    exact Scheme.size_le_of_mono_locallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (j i))

/-! ### The set-theoretic condition for the completion -/

/-- **The completion receives a surjection from an object of the site.** The stages
`Spec (A_i ⧸ K_i ^ (n + 1))` of the completions of the affine charts `W_i = Spec A_i` of `X`,
`K_i` the ideal cutting out the inverse image of `Z`, are jointly surjective onto `X^∧_Z`: a
section of `X^∧_Z` is locally a section of `X` whose inverse image of `Z` is a universal
`n`th-order thickening, locally it lifts to a chart, and there it factors through the `n`th
stage. There are at most `2 ^ size U` of them, each of size at most `size U`, so their disjoint
union is an object of the site, and its representable sheaf is the coproduct of theirs. -/
theorem exists_epi_uliftYoneda_completionSubspace (X : AlgebraicSpaces B S hS)
    (Z : Subfunctor X.1) (hZ : Space.IsClosedSubspace B S hS Z) :
    ∃ (V : BigFppfOver B S hS)
      (t : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj V ⟶
        Space.completionSubspace B S hS X Z), Epi t := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨U, I, W, f, hWaff, -, hlift, -, hI, hWsize⟩ :=
    exists_affine_etale_atlas_sheafifiedULift B S hS X
  -- each chart presented as `Spec A_i`
  have hpres : ∀ i, ∃ (A : Type u) (_ : CommRing A) (hA : B.Contains (Spec (.of A)))
      (str : Spec (.of A) ⟶ S), Nonempty (affineOver B S hS hA str ≅ W i) := by
    intro i
    have := hWaff i
    obtain ⟨A, hCR, hA, str, -, he⟩ := Space.exists_iso_affineOver B S hS (W i)
    exact ⟨A, hCR, hA, str, he⟩
  choose A hCR hA str he using hpres
  let := hCR
  let P : I → BigFppfOver B S hS := fun i ↦ affineOver B S hS (hA i) (str i)
  let e : ∀ i, P i ≅ W i := fun i ↦ Classical.choice (he i)
  let φ : ∀ i, (schemeSpaceFunctor B S hS).obj (P i) ⟶ X :=
    fun i ↦ (schemeSpaceFunctor B S hS).map (e i).hom ≫ f i
  have hG : ∀ i, Space.IsClosedSubspace B S hS
      (Z.preimage (φ i).hom : Subfunctor (yoneda.obj (P i))) := fun i ↦
    Space.isClosedSubspace_preimage B S hS (φ i).hom Z X.property
      (isAlgebraicSpace_yoneda B S hS (P i)) hZ
  let K : ∀ i, Ideal (A i) := fun i ↦
    Space.closedChartRingIdeal B S hS (str i) (hA i)
      (Z.preimage (φ i).hom : Subfunctor (yoneda.obj (P i))) (hG i)
  -- the stages of the chart completions
  let Q : I × ℕ → BigFppfOver B S hS := fun a ↦ (BigAffineFppf.inclusion B S hS).obj
    (quotientOver B S hS (str a.1) (hA a.1) (K a.1 ^ (a.2 + 1)))
  let qA : ∀ a, Q a ⟶ P a.1 := fun a ↦
    Space.quotientToAffineOver B S hS (str a.1) (hA a.1) (K a.1 ^ (a.2 + 1))
  let C := Space.completionSubspaceSubfunctor B S hS X Z
  have hmem : ∀ (a : I × ℕ) {V : BigFppfOver B S hS} (w : V ⟶ Q a),
      (ULift.up ((φ a.1).hom.app (op V) (w ≫ qA a)) :
        (X.1 ⋙ uliftFunctor.{u + 1}).obj (op V)) ∈ C.obj (op V) := fun a V w ↦
    (Space.mem_completionSubspaceSubfunctor_preimage B S hS (φ a.1) Z (op V) _).mp
      (Space.mem_completionSubspaceSubfunctor_of_factor B S hS (str a.1) (hA a.1) _
        (hG a.1) a.2 w)
  let sec : ∀ (a : I × ℕ), C.toFunctor.obj (op (Q a)) := fun a ↦ ⟨_, hmem a (𝟙 _)⟩
  let s : ∀ a, J.uliftYoneda.{u + 1}.obj (Q a) ⟶ Space.completionSubspace B S hS X Z :=
    fun a ↦ J.uliftYonedaEquiv.symm ((J.toSheafify C.toFunctor).app (op (Q a)) (sec a))
  -- the disjoint union of the stages is an object of the site
  have h0 : ℵ₀ ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj U).size :=
    (Scheme.aleph0_le_size _).trans (Cardinal.cantor _).le
  have hlt : 2 ^ ((BigFppfOver.toScheme B S hS).obj U).size < B.cutoff :=
    B.cutoff_isStrongPrelimit U.left.2
  have hcard : #(I × ℕ) ≤ 2 ^ ((BigFppfOver.toScheme B S hS).obj U).size := by
    simp only [Cardinal.mk_prod, Cardinal.lift_uzero, Cardinal.mk_nat, Cardinal.lift_aleph0]
    exact (Cardinal.mul_le_max _ _).trans (max_le (max_le hI h0) h0)
  have hsize : ∀ a, ((BigFppfOver.toScheme B S hS).obj (Q a)).size ≤
      2 ^ ((BigFppfOver.toScheme B S hS).obj U).size := by
    intro a
    have : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (qA a)) := by
      rw [Space.toScheme_map_quotientToAffineOver]
      exact IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have h1 := Scheme.size_le_of_mono_quasiCompact ((BigFppfOver.toScheme B S hS).map (qA a))
    rw [Scheme.size_congr ((BigFppfOver.toScheme B S hS).mapIso (e a.1))] at h1
    exact h1.trans ((hWsize a.1).trans (Cardinal.cantor _).le)
  have hC := B.contains_sigma_of_size_le (fun a ↦ (BigFppfOver.toScheme B S hS).obj (Q a))
    hlt hcard hsize
  let V := BigFppfOver.sigmaObjOfContains B S hS Q hC
  let ι := BigFppfOver.sigmaInclOfContains B S hS Q hC
  let hcol := BigFppfOver.isColimitUliftYonedaSigmaCofanOfContains B S hS Q hC
  let t : J.uliftYoneda.{u + 1}.obj V ⟶ Space.completionSubspace B S hS X Z :=
    Cofan.IsColimit.desc hcol s
  have ht : ∀ a, J.uliftYoneda.{u + 1}.map (ι a) ≫ t = s a := fun a ↦
    Cofan.IsColimit.fac hcol s a
  refine ⟨V, t, ?_⟩
  -- the surjectivity
  rw [← Sheaf.isLocallySurjective_iff_epi]
  constructor
  intro T σ
  refine J.transitive (Presheaf.imageSieve_mem J (J.toSheafify C.toFunctor) σ) _ ?_
  rintro Y h ⟨⟨⟨x⟩, hx⟩, hp⟩
  obtain ⟨R, hR, hRl⟩ := hlift x
  refine J.superset_covering ?_ hR
  intro T' h' hh'
  obtain ⟨i, k, hk⟩ := hRl h' hh'
  let k' : T' ⟶ P i := k ≫ (e i).inv
  have hk' : (φ i).hom.app (op T') k' = X.1.map h'.op x := by
    change (f i).hom.app _ ((k ≫ (e i).inv) ≫ (e i).hom) = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, hk]
  have hmemk : (ULift.up k' : ((yoneda.obj (P i)) ⋙ uliftFunctor.{u + 1}).obj (op T')) ∈
      (Space.completionSubspaceSubfunctor B S hS ((schemeSpaceFunctor B S hS).obj (P i))
        (Z.preimage (φ i).hom)).obj (op T') := by
    refine (Space.mem_completionSubspaceSubfunctor_preimage B S hS (φ i) Z (op T') ⟨k'⟩).mpr ?_
    have hmap := C.map h'.op hx
    have heq : (ULift.up ((φ i).hom.app (op T') k') : (X.1 ⋙ uliftFunctor.{u + 1}).obj (op T')) =
        (X.1 ⋙ uliftFunctor.{u + 1}).map h'.op ⟨x⟩ := ULift.ext hk'
    rw [heq]
    exact hmap
  obtain ⟨n, w, hw⟩ := Space.exists_factor_of_mem_completionSubspaceSubfunctor B S hS (str i)
    (hA i) _ (hG i) k' hmemk
  refine ⟨ULift.up (w ≫ ι (i, n)), ?_⟩
  have key : C.toFunctor.map w.op (sec (i, n)) = C.toFunctor.map h'.op ⟨⟨x⟩, hx⟩ := by
    apply Subtype.ext
    apply ULift.ext
    change X.1.map w.op ((φ i).hom.app _ (𝟙 _ ≫ qA (i, n))) = X.1.map h'.op x
    have nat := NatTrans.naturality_apply (φ i).hom w.op (qA (i, n))
    have hw' : ((schemeSpaceFunctor B S hS).obj (P i)).1.map w.op (qA (i, n)) = k' := hw
    rw [Category.id_comp, ← nat, hw', hk']
  have e1 : t.hom.app (op T') ⟨w ≫ ι (i, n)⟩ = (s (i, n)).hom.app (op T') ⟨w⟩ := by
    rw [← ht (i, n)]
    rfl
  rw [e1]
  change (J.sheafify C.toFunctor).map w.op ((J.toSheafify C.toFunctor).app _ (sec (i, n))) =
    (J.sheafify C.toFunctor).map (h' ≫ h).op σ
  have hc : (J.sheafify C.toFunctor).map (h' ≫ h).op σ =
      (J.sheafify C.toFunctor).map h'.op ((J.sheafify C.toFunctor).map h.op σ) := by
    rw [op_comp]
    exact Functor.map_comp_apply _ _ _ _
  rw [hc, ← hp,
    ← NatTrans.naturality_apply (J.toSheafify C.toFunctor), key]
  exact NatTrans.naturality_apply (J.toSheafify C.toFunctor) h'.op _

/-- **The set-theoretic condition of Stacks 0AIS for the completion `X^∧_Z`** of an algebraic
space along a closed subspace: it receives a surjection from an object of the site
(`AlgebraicGeometry.FormalSpace.exists_epi_uliftYoneda_completionSubspace`), and it is a
subsheaf of the algebraic space `X`
(`AlgebraicGeometry.FormalSpace.mono_completionSubspaceToAmbient`), so the kernel pair of that
surjection is an algebraic space. -/
theorem satisfiesSetTheoreticCondition_completionSubspace (X : AlgebraicSpaces B S hS)
    (Z : Subfunctor X.1) (hZ : Space.IsClosedSubspace B S hS Z) :
    SatisfiesSetTheoreticCondition B S hS (Space.completionSubspace B S hS X Z) := by
  obtain ⟨V, t, ht⟩ := exists_epi_uliftYoneda_completionSubspace B S hS X Z hZ
  have := mono_completionSubspaceToAmbient B S hS X Z
  exact satisfiesSetTheoreticCondition_of_mono_of_epi B S hS X
    (Space.completionSubspaceToAmbient B S hS X Z) V t

/-! ### Stacks 0GXY -/

/-- The atlas of `X` in the form the statements of
`StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionSubspaceLocalTypes` take it, together
with the chart identification of each member's completion. -/
private theorem exists_completionSubspace_chartData {X : AlgebraicSpaces B S hS}
    (Z : Subfunctor X.1) (hZ : Space.IsClosedSubspace B S hS Z) :
    ∃ (I : Type u) (W : I → BigFppfOver B S hS)
      (f : ∀ i, (schemeSpaceFunctor B S hS).obj (W i) ⟶ X),
      (∀ i, (Space.etaleOnSite B S hS).presheaf (f i).hom) ∧
      (∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
        (Space.sheafifiedULiftMap B S hS (f i).hom).hom,
        Space.HasPropertyULift.{u + 1} B S hS
          (fun _ _ q ↦ Space.IsEtaleULift.{u + 1} B S hS q.hom)
          (Space.sheafifiedULiftMap B S hS (f i).hom).hom hfi) ∧
      Sheaf.IsLocallySurjective
        (Sigma.desc fun i : ULift.{u + 1} I ↦ Space.sheafifiedULiftMap B S hS (f i.down).hom) ∧
      ∀ i, ∃ (A : Type u) (_ : CommRing A) (str : Spec (.of A) ⟶ S)
        (hA : B.Contains (Spec (.of A))) (K : Ideal A),
        (∀ _ : _root_.AlgebraicGeometry.IsLocallyNoetherian
          ((BigFppfOver.toScheme B S hS).obj (W i)), IsNoetherianRing A) ∧
        (∀ _ : Space.IsLocallyOfFinitePresentation B S hS Z.ι, K.FG) ∧
        Nonempty (Space.completionSubspace B S hS ((schemeSpaceFunctor B S hS).obj (W i))
          (Z.preimage (f i).hom) ≅ completionAlongIdeal B S hS str hA K) := by
  obtain ⟨-, I, W, f, hWaff, hfet, -, hcov, -, -⟩ :=
    exists_affine_etale_atlas_sheafifiedULift B S hS X
  refine ⟨I, W, f, hfet, fun i ↦ ?_, hcov, fun i ↦ ?_⟩
  · exact exists_hasPropertyULift_sheafifiedULiftMap_of_isEtale B S hS
      (isAlgebraicSpace_yoneda B S hS (W i)) X.property (f i).hom
      ((Space.isEtale_iff_presheaf_of_yoneda B S hS (f i).hom).mpr (hfet i))
  · have := hWaff i
    obtain ⟨A, hCR, str, hA, K, hN, hFG, he⟩ :=
      Space.nonempty_completionSubspaceIsoCompletionAlongIdeal B S hS (W i)
        (Z.preimage (f i).hom)
        (Space.isClosedSubspace_preimage B S hS (f i).hom Z X.property
          (isAlgebraicSpace_yoneda B S hS (W i)) hZ)
    exact ⟨A, hCR, str, hA, K, hN, fun hfp ↦ hFG
      (Space.holdsOnEveryEtaleChart_preimage_ι B S hS _ Z (f i).hom (hfet i) hfp), he⟩

/-- **Stacks 0GXY (1).** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z ⊆ X` be a closed subspace. The completion `X^∧_Z` of `X` along `Z` is *locally weakly
adic*.

The completions of the affine étale charts of `X` along the inverse images of `Z` form an atlas
of `X^∧_Z` (Stacks 0GXV), each is the completion of an affine scheme along an ideal, hence
weakly adic by Stacks 0GXX (1), and `X^∧_Z` satisfies the set-theoretic condition of Stacks
0AIS by `AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_completionSubspace`. -/
@[stacks 0GXY "part (1): locally weakly adic"]
theorem isLocallyWeaklyAdic_completionSubspace_of_isClosedSubspace {X : AlgebraicSpaces B S hS}
    (Z : Subfunctor X.1) (hZ : Space.IsClosedSubspace B S hS Z) :
    IsLocallyWeaklyAdic B S hS (Space.completionSubspace B S hS X Z) := by
  obtain ⟨I, W, f, -, hf, hcov, hchart⟩ := exists_completionSubspace_chartData B S hS Z hZ
  refine isLocallyWeaklyAdic_completionSubspace B S hS Z
    (fun i : ULift.{u + 1} I ↦ (schemeSpaceFunctor B S hS).obj (W i.down))
    (fun i ↦ f i.down) (fun i ↦ hf i.down) hcov (fun i ↦ ?_)
    (satisfiesSetTheoreticCondition_completionSubspace B S hS X Z hZ)
  obtain ⟨A, hCR, str, hA, K, -, -, he⟩ := hchart i.down
  exact ⟨A, hCR, str, hA, K, he⟩

/-- **Stacks 0GXY (2).** Let `S` be a scheme, let `X` be an algebraic space over `S` and let
`Z ⊆ X` be a closed subspace such that `Z ⟶ X` is of finite presentation. The completion
`X^∧_Z` of `X` along `Z` is *locally adic\**.

As in clause (1), with the members of the atlas adic\* by Stacks 0GXX (3): finite presentation
of `Z ⟶ X` makes the ideal cutting out the inverse image of `Z` on an affine chart finitely
generated, `AlgebraicGeometry.Space.fg_closedChartIdeal_of_isLocallyOfFinitePresentation`. -/
@[stacks 0GXY "part (2): locally adic star"]
theorem isLocallyAdicStar_completionSubspace_of_isClosedSubspace {X : AlgebraicSpaces B S hS}
    (Z : Subfunctor X.1) (hZ : Space.IsClosedSubspace B S hS Z)
    (hZfp : Space.IsFinitePresentation B S hS Z.ι) :
    IsLocallyAdicStar B S hS (Space.completionSubspace B S hS X Z) := by
  obtain ⟨I, W, f, -, hf, hcov, hchart⟩ := exists_completionSubspace_chartData B S hS Z hZ
  refine isLocallyAdicStar_completionSubspace B S hS Z
    (fun i : ULift.{u + 1} I ↦ (schemeSpaceFunctor B S hS).obj (W i.down))
    (fun i ↦ f i.down) (fun i ↦ hf i.down) hcov (fun i ↦ ?_)
    (satisfiesSetTheoreticCondition_completionSubspace B S hS X Z hZ)
  obtain ⟨A, hCR, str, hA, K, -, hFG, he⟩ := hchart i.down
  exact ⟨A, hCR, str, hA, K, hFG hZfp.1, he⟩

/-- **Stacks 0GXY (3).** Let `S` be a scheme, let `X` be a locally Noetherian algebraic space
over `S` and let `Z ⊆ X` be a closed subspace. The completion `X^∧_Z` of `X` along `Z` is
*locally Noetherian*.

As in clause (1), with the members of the atlas Noetherian by Stacks 0GXX (4),
`AlgebraicGeometry.FormalSpace.isNoetherian_completionAlongIdeal`: local Noetherianness of `X`
is local in the étale topology (Stacks 03E8), so every étale chart of `X` is a locally
Noetherian scheme and its ring of regular functions is Noetherian. -/
@[stacks 0GXY "part (3): locally Noetherian"]
theorem isLocallyNoetherian_completionSubspace_of_isClosedSubspace {X : AlgebraicSpaces B S hS}
    (Z : Subfunctor X.1) (hZ : Space.IsClosedSubspace B S hS Z)
    (hXN : Space.HasEtaleLocalProperty B S hS X.1
      (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T)) :
    IsLocallyNoetherian B S hS (Space.completionSubspace B S hS X Z) := by
  obtain ⟨I, W, f, hfet, hf, hcov, hchart⟩ := exists_completionSubspace_chartData B S hS Z hZ
  refine isLocallyNoetherian_completionSubspace B S hS Z
    (fun i : ULift.{u + 1} I ↦ (schemeSpaceFunctor B S hS).obj (W i.down))
    (fun i ↦ f i.down) (fun i ↦ hf i.down) hcov (fun i ↦ ?_)
    (satisfiesSetTheoreticCondition_completionSubspace B S hS X Z hZ)
  obtain ⟨A, hCR, str, hA, K, hN, -, he⟩ := hchart i.down
  exact ⟨A, hCR, str, hA, K, hN ((Space.exists_atlas_iff_forall_etale B S hS X.1
    (fun T : Scheme.{u} ↦ _root_.AlgebraicGeometry.IsLocallyNoetherian T) X.property).mp hXN
      (W i.down) (f i.down).hom (hfet i.down)), he⟩

end AlgebraicGeometry.FormalSpace

end
