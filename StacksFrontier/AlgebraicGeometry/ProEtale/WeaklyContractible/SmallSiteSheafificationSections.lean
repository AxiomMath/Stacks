module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.ClopenRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.WeaklyContractible.SheafificationSections
public import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification over an affine weakly contractible object of the small pro-étale site

Let `S` be a scheme and let `ℱ` be a presheaf of sets on the small pro-étale site `S.ProEt`
which sends finite disjoint unions to products. Then the unit `ℱ ⟶ ℱ^#` of sheafification is
bijective on sections over every affine weakly contractible object `W` of `S.ProEt`.

The proof refines an arbitrary covering sieve of `W` by a finite disjoint union decomposition
of `W`. Weak contractibility of `W` makes the ring of global sections of `W` w-contractible:
a faithfully flat weakly étale algebra over it gives a one-element pro-étale covering of `W`
inside `S.ProEt`, over which the identity of `W` lifts, and that lift is a retraction. The
refinement property of Tag 098H then produces, inside any covering sieve of `W`, a finite
family of open immersions into `W` with pairwise disjoint clopen images covering `W`. Such a
family exhibits `W` as the coproduct of its members in `S.ProEt`, because gluing morphisms
along a Zariski cover is unique and the members of the family meet only in schemes with empty
underlying space. The hypothesis on `ℱ` applies to that family, and the general criterion
`CategoryTheory.GrothendieckTopology.bijective_toSheafify_app_of_disjointUnionRefinements`
concludes.

## Main definitions

* `AlgebraicGeometry.Scheme.ProEt.clopenDecompositionObj` and
  `AlgebraicGeometry.Scheme.ProEt.clopenDecompositionHom`: the member of a clopen
  decomposition of the underlying scheme of an object of `S.ProEt`, as an object of `S.ProEt`
  over that object.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.isWContractible_globalSections_of_isWeaklyContractible`:
  an affine weakly contractible object of the small pro-étale site has w-contractible ring of
  global sections.
* `AlgebraicGeometry.Scheme.ProEt.isColimitCofan_clopenDecomposition`: a clopen decomposition
  of the underlying scheme of an object exhibits that object as a coproduct in `S.ProEt`.
* `AlgebraicGeometry.Scheme.ProEt.sieve_ofArrows_clopenDecomposition_mem_topology`: a clopen
  decomposition generates a covering sieve.
* `AlgebraicGeometry.Scheme.ProEt.exists_clopenDecomposition_of_isWContractible`: every
  covering sieve of an affine object with w-contractible global sections contains a clopen
  decomposition of that object.
* `AlgebraicGeometry.Scheme.ProEt.exists_disjointUnionRefinement_of_isWContractible` and
  `AlgebraicGeometry.Scheme.ProEt.exists_disjointUnionRefinement_of_isWeaklyContractible`:
  every covering sieve of an affine object with w-contractible global sections, in particular
  of an affine weakly contractible object, contains a finite disjoint union decomposition of
  that object.
* `AlgebraicGeometry.Scheme.ProEt.bijective_toSheafify_app_of_isWeaklyContractible`: Tag 0F63.

## Implementation notes

Presheaves are valued in `Type (u + 1)`, the universe in which the small pro-étale site of a
scheme in `Scheme.{u}` has sheafification and in which the weak equivalences of presheaves
are the locally bijective morphisms; both are then instances, so the main statement carries no
hypotheses besides those of the source.

## References

* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
* [Stacks Project, Tag 0F63](https://stacks.math.columbia.edu/tag/0F63)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite ProetaleWContractible

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S : Scheme.{u}}

/-- A presieve of `S.ProEt` whose image in `Scheme` is a pro-étale covering of `W.left`
generates a covering sieve of `W`. -/
private theorem generate_mem_topology_of_map_mem (W : S.ProEt) (P : Presieve W)
    (h : P.map (ProEt.forget S ⋙ Over.forget S) ∈ Scheme.proetalePrecoverage.coverings W.left) :
    Sieve.generate P ∈ ProEt.topology S W :=
  Precoverage.generate_mem_toGrothendieck h

/-- An affine object of the small pro-étale site of `S` which is weakly contractible has
w-contractible ring of global sections.

A faithfully flat weakly étale algebra `B` over `A = Γ(W, ⊤)` makes `Spec B → W` a one-element
pro-étale covering of `W` inside `S.ProEt`, so the induced map of representable sheaves is
locally surjective; weak contractibility lifts the identity of `W` through it, and the lift is
a section of `Spec B → Spec A`, hence a retraction of `A → B`. -/
theorem isWContractible_globalSections_of_isWeaklyContractible (W : S.ProEt) [IsAffine W.left]
    (hW : (ProEt.topology S).IsWeaklyContractible W) :
    IsWContractible.{u, u} Γ(W.left, ⊤) := by
  intro B _ _ hwe hff
  let A := Γ(W.left, ⊤)
  let r : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let f₀ := Scheme.Spec.map r.op
  let f : Scheme.Spec.obj (op (CommRingCat.of B)) ⟶ W.left := f₀ ≫ W.left.isoSpec.inv
  have hffhom : r.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  have hFlat : Flat f₀ := ((flat_and_surjective_SpecMap_iff r).mpr hffhom).1
  have hDiagFlat : Flat (pullback.diagonal f₀) := by
    change Flat (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    rw [diagonal_SpecMap A B]
    have h₁ : Flat
        (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.lmul' A (S := B)).toRingHom)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact hwe.2
    exact MorphismProperty.comp_mem _ _ _ h₁ inferInstance
  have hWE₀ : WeaklyEtale f₀ := (weaklyEtale_iff _).mpr ⟨hFlat, hDiagFlat⟩
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  have hWE : WeaklyEtale f := by
    have _ : WeaklyEtale f₀ := hWE₀
    have _ : WeaklyEtale W.left.isoSpec.inv := MorphismProperty.of_isIso @WeaklyEtale _
    dsimp only [f]; infer_instance
  have hSurj₀ : Surjective f₀ := ((flat_and_surjective_SpecMap_iff r).mpr hffhom).2
  have hSurj : Surjective f := by
    refine ⟨fun x ↦ ?_⟩
    obtain ⟨y, hy⟩ := hSurj₀.surj (W.left.isoSpec.hom x)
    refine ⟨y, ?_⟩
    change W.left.isoSpec.inv.base (f₀.base y) = x
    rw [hy]
    simp
  have hQC : QuasiCompact f := by dsimp only [f]; infer_instance
  have hcov : Presieve.singleton f ∈ Scheme.proetalePrecoverage.coverings W.left := by
    have _ : Surjective f := hSurj
    have _ : QuasiCompact f := hQC
    simpa only [Scheme.proetalePrecoverage] using
      (Scheme.Hom.singleton_mem_propQCPrecoverage hWE :
        Presieve.singleton f ∈ Scheme.propQCPrecoverage @WeaklyEtale W.left)
  have hWEf : WeaklyEtale (f ≫ W.hom) := by
    have _ : WeaklyEtale f := hWE
    infer_instance
  let V : S.ProEt := @Scheme.ProEt.mk S _ (f ≫ W.hom) hWEf
  let g : V ⟶ W := MorphismProperty.Over.homMk f rfl
  let J := ProEt.topology S
  have hcovS : Sieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ g) ∈ J W := by
    have hpre : Presieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ g) = Presieve.singleton g := by
      funext Y a
      refine propext ⟨?_, ?_⟩
      · rintro ⟨_⟩; exact Presieve.singleton.mk
      · rintro ⟨⟩; exact Presieve.ofArrows.mk ()
    rw [show Sieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ g) = Sieve.generate
      (Presieve.singleton g) from congrArg Sieve.generate hpre]
    refine generate_mem_topology_of_map_mem _ _ ?_
    rw [Presieve.map_singleton]
    exact hcov
  have hls : Sheaf.IsLocallySurjective (J.yoneda.map g) := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff]
    rw [show (sheafToPresheaf J (Type u)).map (J.yoneda.map g) = yoneda.map g from
      J.yoneda_map_hom g]
    refine ⟨?_⟩
    intro T s
    have hsub : (Sieve.ofArrows (fun _ : Unit ↦ V) (fun _ ↦ g)).pullback s ≤
        Presheaf.imageSieve (yoneda.map g) s := by
      intro Y a ha
      rw [Sieve.pullback_apply, Sieve.mem_ofArrows_iff] at ha
      obtain ⟨_, q, hcomp⟩ := ha
      exact ⟨q, hcomp.symm⟩
    exact J.superset_covering hsub (J.pullback_stable s hcovS)
  obtain ⟨t, ht⟩ := hW _ _ (J.yoneda.map g) hls (𝟙 W)
  have happ : ((sheafToPresheaf J (Type u)).map (J.yoneda.map g)).app (op W) t = t ≫ g := by
    change (J.yoneda.map g).hom.app (op W) t = t ≫ g
    rw [J.yoneda_map_hom, yoneda_map_app]
    rfl
  rw [happ] at ht
  have hcomp : ((ProEt.forget S).map t).left ≫ f = 𝟙 W.left := by
    have h : (ProEt.forget S).map t ≫ (ProEt.forget S).map g =
        𝟙 ((ProEt.forget S).obj W) := by
      rw [← Functor.map_comp, ht]
      exact (ProEt.forget S).map_id W
    have h' : ((ProEt.forget S).map t).left ≫ ((ProEt.forget S).map g).left =
        𝟙 ((ProEt.forget S).obj W).left := by
      simpa only [Over.comp_left, Over.id_left] using
        congrArg (fun q : (ProEt.forget S).obj W ⟶ (ProEt.forget S).obj W ↦ q.left) h
    exact h'
  have h₀ : ((ProEt.forget S).map t).left ≫ f₀ = W.left.isoSpec.hom :=
    (cancel_mono W.left.isoSpec.inv).1
      ((Category.assoc _ _ _).trans (hcomp.trans W.left.isoSpec.hom_inv_id.symm))
  refine hasRetraction_of_section A B
    (W.left.isoSpec.inv ≫ ((ProEt.forget S).map t).left) ?_
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q ↦ W.left.isoSpec.inv ≫ q) h₀).trans W.left.isoSpec.inv_hom_id)

/-- The `i`-th member of a finite family of morphisms into the underlying scheme of an object
`W` of `S.ProEt`, viewed as an object of `S.ProEt` through the composite with the structure
morphism of `W`. -/
def clopenDecompositionObj (W : S.ProEt) {n : ℕ} {U : Fin n → Scheme.{u}}
    (f : (i : Fin n) → U i ⟶ W.left) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) (i : Fin n) :
    S.ProEt :=
  @Scheme.ProEt.mk S (U i) (f i ≫ W.hom) (hf i)

/-- The `i`-th member of such a family, as a morphism of `S.ProEt` to `W`. -/
def clopenDecompositionHom (W : S.ProEt) {n : ℕ} {U : Fin n → Scheme.{u}}
    (f : (i : Fin n) → U i ⟶ W.left) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) (i : Fin n) :
    clopenDecompositionObj W f hf i ⟶ W :=
  MorphismProperty.Over.homMk (f i) rfl

/-- A finite family of open immersions into the underlying scheme of an object `W` of `S.ProEt`
whose images are pairwise disjoint clopen subsets covering `W` exhibits `W` as the coproduct of
the corresponding objects of `S.ProEt`.

A cone on the family is glued along the Zariski cover it provides; compatibility of the gluing
data is automatic, since two distinct members have disjoint images and so their fibre product
has empty underlying space. -/
noncomputable def isColimitCofan_clopenDecomposition (W : S.ProEt) {n : ℕ}
    {U : Fin n → Scheme.{u}} (f : (i : Fin n) → U i ⟶ W.left)
    (hdec : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) :
    IsColimit (Cofan.mk W (clopenDecompositionHom W f hf)) := by
  classical
  let cover : W.left.OpenCover := Scheme.Cover.mkOfCovers (Fin n) U f
    (fun x ↦ by
      have hx : x ∈ ⋃ i, Set.range (f i).base := by rw [hdec.cover]; trivial
      simpa only [Set.mem_iUnion, Set.mem_range] using hx)
    hdec.openImmersion
  have hCompat (c : Cofan (clopenDecompositionObj W f hf)) : ∀ i j,
      pullback.fst (cover.f i) (cover.f j) ≫ ((ProEt.forget S).map (c.inj i)).left =
        pullback.snd (cover.f i) (cover.f j) ≫ ((ProEt.forget S).map (c.inj j)).left := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have _ : Mono (cover.f i) := (hdec.openImmersion i).mono
      rw [fst_eq_snd_of_mono_eq]
    · have hZ : IsEmpty (pullback (cover.f i) (cover.f j) : Scheme).carrier :=
        Scheme.isEmpty_pullback (cover.f i) (cover.f j) (hdec.disjoint i j hij)
      obtain ⟨hinit⟩ := AlgebraicGeometry.isInitial_iff_isEmpty.mpr hZ
      exact hinit.hom_ext _ _
  refine Cofan.IsColimit.mk _ (fun c ↦ ?_) (fun c i ↦ ?_) (fun c m hm ↦ ?_)
  · refine MorphismProperty.Over.homMk (cover.glueMorphisms
      (fun i ↦ ((ProEt.forget S).map (c.inj i)).left) (hCompat c)) ?_
    refine cover.hom_ext _ _ fun i ↦ ?_
    refine (congrArg (fun a ↦ a ≫ c.pt.hom)
      (cover.ι_glueMorphisms _ (hCompat c) i)).trans ?_
    exact ((ProEt.forget S).map (c.inj i)).w
  · refine (ProEt.forgetFullyFaithful S).map_injective ?_
    ext
    exact cover.ι_glueMorphisms _ (hCompat c) i
  · refine (ProEt.forgetFullyFaithful S).map_injective ?_
    ext
    refine cover.hom_ext _ _ fun i ↦ ?_
    refine (congrArg (fun k ↦ ((ProEt.forget S).map k).left) (hm i)).trans ?_
    exact (cover.ι_glueMorphisms _ (hCompat c) i).symm

/-- A clopen decomposition of the underlying scheme of an object `W` of `S.ProEt` generates a
covering sieve of `W`: it is a Zariski cover, hence a pro-étale cover, of `W.left`. -/
theorem sieve_ofArrows_clopenDecomposition_mem_topology (W : S.ProEt) {n : ℕ}
    {U : Fin n → Scheme.{u}} (f : (i : Fin n) → U i ⟶ W.left)
    (hdec : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)) :
    Sieve.ofArrows (clopenDecompositionObj W f hf) (clopenDecompositionHom W f hf) ∈
      ProEt.topology S W := by
  have hzar : Presieve.ofArrows U f ∈ Scheme.zariskiPrecoverage W.left := by
    refine (Scheme.ofArrows_mem_precoverage_iff _).mpr ⟨fun x ↦ ?_, hdec.openImmersion⟩
    have hx : x ∈ ⋃ i, Set.range (f i).base := by rw [hdec.cover]; trivial
    simpa only [Set.mem_iUnion] using hx
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  refine generate_mem_topology_of_map_mem _ _ ?_
  rw [Presieve.map_ofArrows]
  exact Scheme.zariskiPrecoverage_le_propQCPrecoverage _ hzar

/-- Every covering sieve of an affine object `W` of the small pro-étale site of `S` whose ring
of global sections is w-contractible contains a *clopen decomposition* of `W`: a finite family
of open immersions into `W.left` with pairwise disjoint clopen images covering `W.left`, each
of whose members, viewed as an object of `S.ProEt` over `W`, lies in the sieve.

This is the refinement property of Tag 098H: the sieve is pushed forward to a pro-étale
covering sieve of the spectrum of the w-contractible ring `Γ(W, ⊤)`, where it is refined by a
clopen decomposition, and the members of that decomposition are open subschemes of `W`, hence
again objects of `S.ProEt`. -/
theorem exists_clopenDecomposition_of_isWContractible (W : S.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) (R : Sieve W)
    (hR : R ∈ ProEt.topology S W) :
    ∃ (n : ℕ) (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ W.left)
      (_hdec : IsClopenDecompositionCover U f) (hf : ∀ i, WeaklyEtale (f i ≫ W.hom)),
      ∀ i, R.arrows (clopenDecompositionHom W f hf i) := by
  classical
  set G := ProEt.forget S ⋙ Over.forget S with hG
  have hpush : R.functorPushforward G ∈ Scheme.proetaleTopology.{u} W.left :=
    (CoverPreserving.of_isContinuous G (ProEt.topology S) Scheme.proetaleTopology).cover_preserve
      hR
  let e : specOf Γ(W.left, ⊤) ≅ W.left := W.left.isoSpec.symm
  obtain ⟨n, U, f, hdec, href⟩ :=
    everyProetaleCoverHasZariskiRefinement_of_wContractible Γ(W.left, ⊤)
      hW ((R.functorPushforward G).pullback e.hom)
      (Scheme.proetaleTopology.pullback_stable e.hom hpush)
  have hdec' : IsClopenDecompositionCover U (fun i ↦ f i ≫ e.hom) :=
    IsClopenDecompositionCover.comp_iso e U f hdec
  have hf : ∀ i, WeaklyEtale ((f i ≫ e.hom) ≫ W.hom) := by
    intro i
    have _ : IsOpenImmersion (f i ≫ e.hom) := hdec'.openImmersion i
    infer_instance
  refine ⟨n, U, fun i ↦ f i ≫ e.hom, hdec', hf, fun i ↦ ?_⟩
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
  rw [← hab]
  exact R.downward_closed hb a

/-- Every covering sieve of an affine object `W` of the small pro-étale site of `S` whose ring
of global sections is w-contractible contains a finite family of objects of that site which
exhibits `W` as their coproduct and generates a covering sieve: the clopen decomposition of
`exists_clopenDecomposition_of_isWContractible`. -/
theorem exists_disjointUnionRefinement_of_isWContractible (W : S.ProEt) [IsAffine W.left]
    (hW : IsWContractible.{u, u} Γ(W.left, ⊤)) (R : Sieve W)
    (hR : R ∈ ProEt.topology S W) :
    ∃ (n : ℕ) (V : Fin n → S.ProEt) (g : (i : Fin n) → V i ⟶ W)
      (_ : IsColimit (Cofan.mk W g)),
      Sieve.ofArrows V g ∈ ProEt.topology S W ∧ ∀ i, R.arrows (g i) := by
  obtain ⟨n, U, f, hdec, hf, hR'⟩ := exists_clopenDecomposition_of_isWContractible W hW R hR
  exact ⟨n, clopenDecompositionObj W f hf, clopenDecompositionHom W f hf,
    isColimitCofan_clopenDecomposition W f hdec hf,
    sieve_ofArrows_clopenDecomposition_mem_topology W f hdec hf, hR'⟩

/-- Every covering sieve of an affine weakly contractible object `W` of the small pro-étale
site of `S` contains a finite family of objects of that site which exhibits `W` as their
coproduct and generates a covering sieve: the ring of global sections of `W` is w-contractible
(`isWContractible_globalSections_of_isWeaklyContractible`), so
`exists_disjointUnionRefinement_of_isWContractible` applies. -/
theorem exists_disjointUnionRefinement_of_isWeaklyContractible (W : S.ProEt) [IsAffine W.left]
    (hW : (ProEt.topology S).IsWeaklyContractible W) (R : Sieve W)
    (hR : R ∈ ProEt.topology S W) :
    ∃ (n : ℕ) (V : Fin n → S.ProEt) (g : (i : Fin n) → V i ⟶ W)
      (_ : IsColimit (Cofan.mk W g)),
      Sieve.ofArrows V g ∈ ProEt.topology S W ∧ ∀ i, R.arrows (g i) :=
  exists_disjointUnionRefinement_of_isWContractible W
    (isWContractible_globalSections_of_isWeaklyContractible W hW) R hR

/-- **Stacks 0F63.** Let `S` be a scheme and let `ℱ` be a presheaf of sets on the small
pro-étale site of `S` which sends finite disjoint unions to products. Then the unit of
sheafification is bijective on sections over every affine weakly contractible object `W`, so
that `ℱ^#(W) = ℱ(W)`. -/
@[stacks 0F63 "sheafification does not change sections over an affine weakly contractible object"]
theorem bijective_toSheafify_app_of_isWeaklyContractible (F : S.ProEtᵒᵖ ⥤ Type (u + 1))
    (hF : GrothendieckTopology.SendsFiniteDisjointUnionsToProducts F) (W : S.ProEt)
    [IsAffine W.left] (hW : (ProEt.topology S).IsWeaklyContractible W) :
    Function.Bijective ((toSheafify (ProEt.topology S) F).app (op W)) :=
  GrothendieckTopology.bijective_toSheafify_app_of_disjointUnionRefinements _ F hF W
    (exists_disjointUnionRefinement_of_isWeaklyContractible W hW)

end AlgebraicGeometry.Scheme.ProEt

end
