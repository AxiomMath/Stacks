module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Henselization

/-!
# Clopen decompositions in the small pro-étale site and the site `S_app`

Let `S` be a scheme. A *clopen decomposition* of an object `W` of the small pro-étale site of
`S` is a finite family of morphisms `V_k ⟶ W` whose underlying morphisms of schemes are open
immersions with pairwise disjoint clopen images covering `W`. A sheaf of sets on the small
pro-étale site sends a clopen decomposition to a product, because the family is a covering and
two of its distinct members meet only in the empty scheme. Every covering sieve of an affine
weakly contractible object contains a clopen decomposition of it (Stacks 098H), and a member of a
clopen decomposition of an object of `S_app` — the affine objects with ind-étale ring of global
sections of Stacks 098X — is again an object of `S_app`.

## Main definitions

* `AlgebraicGeometry.ProEtale.AppSmallProetale.inducedTopology`: the topology on `S_app`
  induced from the small pro-étale site.

## Main results

* `AlgebraicGeometry.ProEtale.bijective_sections_of_isClopenDecompositionCover`: a sheaf of sets
  on the small pro-étale site sends a clopen decomposition to a product.
* `AlgebraicGeometry.ProEtale.AppSmallProetale.bijective_sections_of_isClopenDecompositionCover`:
  the same for a sheaf of sets on `S_app` with the topology induced from the small pro-étale
  site.
* `AlgebraicGeometry.ProEtale.isAppSmall_of_isOpenImmersion_of_isClosed`: a clopen piece of an
  object of `S_app` is an object of `S_app`.
* `AlgebraicGeometry.Scheme.ProEt.exists_clopenDecomposition_of_isWeaklyContractible`: every
  covering sieve of an affine weakly contractible object of the small pro-étale site contains a
  clopen decomposition of that object.

## References

* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u w

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- **Clopen refinements at an affine weakly contractible object.** Every covering sieve of an
affine weakly contractible object `W` of the small pro-étale site of `S` contains the members of
a clopen decomposition of `W`: a finite family of open immersions into `W.left` with pairwise
disjoint clopen images covering `W.left`, viewed as objects of the small pro-étale site over
`W`.

This is the refinement property of Tag 098H, as in
`AlgebraicGeometry.Scheme.ProEt.exists_disjointUnionRefinement_of_isWeaklyContractible`, but
remembering the clopen decomposition itself rather than only the coproduct it forms. -/
theorem exists_clopenDecomposition_of_isWeaklyContractible (W : S.ProEt) [IsAffine W.left]
    (hW : (ProEt.topology S).IsWeaklyContractible W) (R : Sieve W)
    (hR : R ∈ ProEt.topology S W) :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ W.left)
      (_ : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)),
      ∀ i, R.arrows (clopenDecompositionHom W f hf i) := by
  classical
  set G := ProEt.forget S ⋙ Over.forget S with hG
  have hpush : R.functorPushforward G ∈ Scheme.proetaleTopology.{u} W.left :=
    (CoverPreserving.of_isContinuous G (ProEt.topology S) Scheme.proetaleTopology).cover_preserve
      hR
  let e : specOf Γ(W.left, ⊤) ≅ W.left := W.left.isoSpec.symm
  obtain ⟨n, U, f, hdec, href⟩ :=
    everyProetaleCoverHasZariskiRefinement_of_wContractible Γ(W.left, ⊤)
      (isWContractible_globalSections_of_isWeaklyContractible W hW)
      ((R.functorPushforward G).pullback e.hom)
      (Scheme.proetaleTopology.pullback_stable e.hom hpush)
  have hdec' : IsClopenDecompositionCover U (fun i ↦ f i ≫ e.hom) :=
    IsClopenDecompositionCover.comp_iso e U f hdec
  have hf : ∀ i, WeaklyEtale ((f i ≫ e.hom) ≫ W.hom) := by
    intro i
    have _ : IsOpenImmersion (f i ≫ e.hom) := hdec'.openImmersion i
    infer_instance
  refine ⟨n, U, _, hdec', hf, fun i ↦ ?_⟩
  obtain ⟨Z, b, lift, hb, hfac⟩ := Presieve.getFunctorPushforwardStructure (href i)
  have hfac' : f i ≫ e.hom = lift ≫ ((ProEt.forget S).map b).left := hfac
  have hlift : lift ≫ Z.hom = (clopenDecompositionObj W (fun i ↦ f i ≫ e.hom) hf i).hom :=
    (congrArg (fun q ↦ lift ≫ q) ((ProEt.forget S).map b).w.symm).trans
      ((Category.assoc lift _ W.hom).symm.trans
        (congrArg (fun q ↦ q ≫ W.hom) hfac'.symm))
  let a : clopenDecompositionObj W (fun i ↦ f i ≫ e.hom) hf i ⟶ Z :=
    MorphismProperty.Over.homMk lift hlift
  have hab : a ≫ b = clopenDecompositionHom W (fun i ↦ f i ≫ e.hom) hf i := by
    refine (ProEt.forgetFullyFaithful S).map_injective ?_
    ext
    exact hfac'.symm
  exact hab ▸ R.downward_closed hb a

end AlgebraicGeometry.Scheme.ProEt

namespace AlgebraicGeometry.ProEtale

/-- The topology on the site `S_app` of affine objects with ind-étale ring of global sections
induced from the small pro-étale site of `S`; for `S` affine, restriction of sheaves along the
inclusion is an equivalence of topoi for it (Stacks 098X). -/
abbrev AppSmallProetale.inducedTopology (S : Scheme.{u}) :
    GrothendieckTopology (AppSmallProetale S) :=
  (AppSmallProetale.inclusion S).inducedTopology (Scheme.ProEt.topology S)

/-! ### Sheaves send clopen decompositions to products -/

/-- A sheaf of sets sends a covering family of monomorphisms to a product, provided any two
distinct members only overlap in objects `T` with `⊥ ∈ J T`. -/
private theorem bijective_sections_of_sieve_mem_of_bot_mem {C : Type*} [Category C]
    (J : GrothendieckTopology C) (F : Cᵒᵖ ⥤ Type w) (hF : Presheaf.IsSheaf J F)
    {W : C} {n : ℕ} {V : Fin n → C} (g : (k : Fin n) → V k ⟶ W)
    (hcov : Sieve.ofArrows V g ∈ J W) [∀ k, Mono (g k)]
    (hbot : ∀ i j, i ≠ j → ∀ (T : C) (a : T ⟶ V i) (b : T ⟶ V j), a ≫ g i = b ≫ g j →
      (⊥ : Sieve T) ∈ J T) :
    Function.Bijective (fun (x : F.obj (op W)) (k : Fin n) ↦ F.map (g k).op x) := by
  have hsh : Presieve.IsSheafFor F (Presieve.ofArrows V g) := by
    have := ((isSheaf_iff_isSheaf_of_type _ F).mp hF) _ hcov
    rwa [Sieve.ofArrows, ← Presieve.isSheafFor_iff_generate] at this
  rw [Presieve.isSheafFor_arrows_iff] at hsh
  have hcompat (x : (k : Fin n) → F.obj (op (V k))) : Presieve.Arrows.Compatible F g x := by
    intro i j T a b hab
    by_cases hij : i = j
    · subst hij
      rw [cancel_mono] at hab
      rw [hab]
    · have hterm : IsTerminal (F.obj (op T)) :=
        Sheaf.isTerminalOfBotCover ⟨F, hF⟩ T (hbot i j hij T a b hab)
      let := Types.isTerminalEquivUnique _ hterm
      exact Subsingleton.elim _ _
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨t, _, ht⟩ := hsh (fun k ↦ F.map (g k).op x) (hcompat _)
    exact (ht x (fun k ↦ rfl)).trans (ht y (fun k ↦ (congrFun hxy k).symm)).symm
  · obtain ⟨t, ht, _⟩ := hsh x (hcompat x)
    exact ⟨t, funext ht⟩

/-- **A sheaf sends a clopen decomposition to a product.** Let `F` be a sheaf of sets on the
small pro-étale site of `S` and let `g k : V k ⟶ W` be a finite family of morphisms whose
underlying morphisms of schemes form a clopen decomposition cover of `W`. Then the sections of
`F` over `W` are the families of sections over the `V k`.

The family generates a covering sieve, being a Zariski covering. A family of sections over the
`V k` is automatically compatible: two distinct members of the family meet only in the empty
scheme, over which `F` has a single section, and each member is a monomorphism. -/
theorem bijective_sections_of_isClopenDecompositionCover {S : Scheme.{u}}
    (F : S.ProEtᵒᵖ ⥤ Type w) (hF : Presheaf.IsSheaf (Scheme.ProEt.topology S) F)
    {W : S.ProEt} {n : ℕ} {V : Fin n → S.ProEt} (g : (k : Fin n) → V k ⟶ W)
    (hdec : IsClopenDecompositionCover (fun k ↦ (V k).left) (fun k ↦ (g k).left)) :
    Function.Bijective (fun (x : F.obj (op W)) (k : Fin n) ↦ F.map (g k).op x) := by
  classical
  have hsurj : ∀ x : W.left, ∃ k y, (g k).hom.left.base y = x := by
    intro x
    have hx : x ∈ ⋃ k, Set.range (g k).left.base := by rw [hdec.cover]; trivial
    exact Set.mem_iUnion.mp hx
  have hcov : Sieve.ofArrows V g ∈ Scheme.ProEt.topology S W :=
    sieve_ofArrows_mem_proetaleTopology_of_isOpenImmersion V g hdec.openImmersion hsurj
  have hmono (k : Fin n) : Mono (g k) := by
    have _ := hdec.openImmersion k
    have : Mono ((Scheme.ProEt.forget S ⋙ Over.forget S).map (g k)) :=
      inferInstanceAs (Mono (g k).left)
    exact (Scheme.ProEt.forget S ⋙ Over.forget S).mono_of_mono_map this
  refine bijective_sections_of_sieve_mem_of_bot_mem _ F hF g hcov fun i j hij T a b hab ↦ ?_
  have hT : IsEmpty T.left := by
    refine ⟨fun t ↦ ?_⟩
    have h1 : (g i).left.base (a.left.base t) = (g j).left.base (b.left.base t) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun q : T ⟶ W ↦ q.left.base t) hab
    exact Set.disjoint_iff.mp (hdec.disjoint i j hij) ⟨⟨_, rfl⟩, ⟨_, h1.symm⟩⟩
  exact Scheme.ProEt.bot_mem_topology T

/-! ### Members of clopen decompositions of objects of `S_app` -/

/-- **A clopen piece of an object of `S_app` is an object of `S_app`.** Let `W` be an object of
the small pro-étale site of `S` which is affine with ind-étale ring of global sections, and let
`f : U ⟶ W.left` be an open immersion with closed image. Then `U` is affine, being a closed
subscheme of `W.left`, and its ring of global sections is ind-étale over that of `S`, being étale
over that of `W.left`. -/
theorem isAppSmall_of_isOpenImmersion_of_isClosed {S : Scheme.{u}} {W : S.ProEt}
    (hW : IsAppSmall S W) {U : Scheme.{u}} (f : U ⟶ W.left) [IsOpenImmersion f]
    (hf : IsClosed (Set.range f.base)) [WeaklyEtale (f ≫ W.hom)] :
    IsAppSmall S (Scheme.ProEt.mk (f ≫ W.hom)) := by
  have _ : IsAffine W.left := hW.1
  have _ : IsClosedImmersion f := IsClosedImmersion.of_isPreimmersion f hf
  have _ : IsAffine U := isAffine_of_isAffineHom f
  refine ⟨‹IsAffine U›, ?_⟩
  let _ : Algebra Γ(S, ⊤) Γ(W.left, ⊤) := W.hom.appTop.hom.toAlgebra
  let _ : Algebra Γ(W.left, ⊤) Γ(U, ⊤) := f.appTop.hom.toAlgebra
  let _ : Algebra Γ(S, ⊤) Γ(U, ⊤) := (f ≫ W.hom).appTop.hom.toAlgebra
  have _ : IsScalarTower Γ(S, ⊤) Γ(W.left, ⊤) Γ(U, ⊤) := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    change (f ≫ W.hom).appTop.hom a = f.appTop.hom (W.hom.appTop.hom a)
    rw [Scheme.Hom.comp_appTop]
    rfl
  have hét : Algebra.Etale Γ(W.left, ⊤) Γ(U, ⊤) :=
    (HasRingHomProperty.appTop @Etale f inferInstance : f.appTop.hom.Etale).toAlgebra
  exact StacksDraft.indEtale_comp (A := Γ(S, ⊤)) (B := Γ(W.left, ⊤)) (C := Γ(U, ⊤)) hW.2
    (indEtale_of_etale hét)

/-- **A sheaf on `S_app` sends a clopen decomposition to a product.** The same statement as
`bijective_sections_of_isClopenDecompositionCover`, for a sheaf of sets on `S_app` with the
topology induced from the small pro-étale site. -/
theorem AppSmallProetale.bijective_sections_of_isClopenDecompositionCover {S : Scheme.{u}}
    [IsAffine S] (F : (AppSmallProetale S)ᵒᵖ ⥤ Type w)
    (hF : Presheaf.IsSheaf (AppSmallProetale.inducedTopology S) F)
    {W : AppSmallProetale S} {n : ℕ} {V : Fin n → AppSmallProetale S} (g : (k : Fin n) → V k ⟶ W)
    (hdec : IsClopenDecompositionCover (fun k ↦ (V k).obj.left) (fun k ↦ (g k).hom.left)) :
    Function.Bijective (fun (x : F.obj (op W)) (k : Fin n) ↦ F.map (g k).op x) := by
  classical
  let ι := AppSmallProetale.inclusion S
  have hsurj : ∀ x : W.obj.left, ∃ k y, (ι.map (g k)).hom.left.base y = x := by
    intro x
    have hx : x ∈ ⋃ k, Set.range (g k).hom.left.base := by rw [hdec.cover]; trivial
    exact Set.mem_iUnion.mp hx
  have hcov₀ : Sieve.ofArrows (fun k ↦ ι.obj (V k)) (fun k ↦ ι.map (g k)) ∈
      Scheme.ProEt.topology S (ι.obj W) :=
    sieve_ofArrows_mem_proetaleTopology_of_isOpenImmersion _ _ hdec.openImmersion hsurj
  have hcov : Sieve.ofArrows V g ∈ AppSmallProetale.inducedTopology S W := by
    refine (ι.functorPushforward_mem_iff (AppSmallProetale.inducedTopology S)
      (Scheme.ProEt.topology S)).mp ((Scheme.ProEt.topology S).superset_covering ?_ hcov₀)
    rintro T f hf
    obtain ⟨k, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hf
    exact ⟨V k, g k, a, Sieve.ofArrows_mk _ _ k, rfl⟩
  have hmono (k : Fin n) : Mono (g k) := by
    have _ := hdec.openImmersion k
    have : Mono ((ι ⋙ Scheme.ProEt.forget S ⋙ Over.forget S).map (g k)) :=
      inferInstanceAs (Mono (g k).hom.left)
    exact (ι ⋙ Scheme.ProEt.forget S ⋙ Over.forget S).mono_of_mono_map this
  refine bijective_sections_of_sieve_mem_of_bot_mem _ F hF g hcov fun i j hij T a b hab ↦ ?_
  have hT : IsEmpty T.obj.left := by
    refine ⟨fun t ↦ ?_⟩
    have h1 : (g i).hom.left.base (a.hom.left.base t) =
        (g j).hom.left.base (b.hom.left.base t) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      exact congrArg (fun q : T ⟶ W ↦ q.hom.left.base t) hab
    exact Set.disjoint_iff.mp (hdec.disjoint i j hij) ⟨⟨_, rfl⟩, ⟨_, h1.symm⟩⟩
  refine (ι.functorPushforward_mem_iff (AppSmallProetale.inducedTopology S)
    (Scheme.ProEt.topology S)).mp ?_
  rw [Sieve.functorPushforward_bot]
  have : IsEmpty (ι.obj T).left := hT
  exact Scheme.ProEt.bot_mem_topology (ι.obj T)

end AlgebraicGeometry.ProEtale

end

