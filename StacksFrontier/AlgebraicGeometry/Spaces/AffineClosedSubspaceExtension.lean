module

public import StacksFrontier.AlgebraicGeometry.FiniteTypeIdealSheafDirected.Capture
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealBijection
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceRange
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.ClosedImmersionFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending finitely presented closed subspaces of an affine algebraic space

Let `Y` be an affine algebraic space over a scheme `S`, let `U₁, …, Uₙ ⊆ Y` be quasi-compact
open subspaces and let `Tᵢ ⊆ Uᵢ` be closed subspaces of finite presentation which agree on the
overlaps.  Then there is one closed subspace `T' ⊆ Y` of finite presentation with
`T' ∩ Uᵢ = Tᵢ` for every `i`.  This is the base case of the extension of finitely presented
closed subspaces from quasi-compact opens of a quasi-compact and quasi-separated algebraic space,
which the induction principle of Stacks 08GP propagates.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.exists_isFiniteType_comap_eq`: the case of an affine
  scheme `X`.  Finite type ideal sheaves `Iᵢ` on finitely many quasi-compact opens of `X` whose
  closed subschemes agree on the overlaps are the restrictions of one finite type ideal sheaf
  on `X`.
* `AlgebraicGeometry.Space.exists_closedSubspace_extension_of_isAffineSpace`: the same for an
  affine algebraic space and its closed subspaces.

## Implementation notes

On the scheme `X` the ideal sheaf `K = ⨅ᵢ (Iᵢ)_*` of functions vanishing on every `V(Iᵢ)`
restricts to `Iᵢ` on the `i`-th open, by the compatibility on the overlaps.  It need not be of
finite type, but the finitely many generators of the `Iᵢ` over a finite affine cover of each
open lie in a finite type `J ≤ K`, by the capture lemma
`Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_forall_mem`, and then `J` restricts to `Iᵢ`
as well.

The algebraic space `Y` is identified with the functor of points of an affine scheme `X₀` of
the site.  The opens `Uᵢ` and the closed subspaces `Tᵢ` are read on `X₀` through their
represented base changes, and the comparison of subspaces of `Y` with subschemes of `X₀` is made
on functors of points, with `AlgebraicGeometry.Space.subschemePoints` and its injectivity on
immersed subschemes.  Finite presentation passes between the two sides by the chart form of
Stacks 084Q.

## References

* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 084Q](https://stacks.math.columbia.edu/tag/084Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The inverse image of a finite infimum of ideal sheaves along an open immersion is the
infimum of the inverse images. -/
theorem comap_iInf_of_isOpenImmersion {V : Scheme.{u}} (a : V ⟶ X) [IsOpenImmersion a]
    {ι : Type*} [Finite ι] (M : ι → X.IdealSheafData) :
    (⨅ i, M i).comap a = ⨅ i, (M i).comap a := by
  refine IdealSheafData.ext (funext fun W => ?_)
  simp only [ideal_comap_of_isOpenImmersion, ideal_iInf, iInf_apply, Ideal.comap_iInf]

/-- The direct image along `f` of an ideal sheaf, pulled back along an open immersion `a`, is
the kernel of the base change of `I.subschemeι ≫ f` along `a`. -/
theorem comap_map_eq_ker_pullback_snd {V Z : Scheme.{u}} (I : Z.IdealSheafData) (f : Z ⟶ X)
    [QuasiCompact (I.subschemeι ≫ f)] (a : V ⟶ X) [IsOpenImmersion a] :
    (I.map f).comap a = (pullback.snd (I.subschemeι ≫ f) a).ker := by
  refine IdealSheafData.ext (funext fun W => ?_)
  rw [ideal_comap_of_isOpenImmersion,
    ker_ideal_of_isPullback_of_isOpenImmersion (I.subschemeι ≫ f) (pullback.snd _ a)
      (pullback.fst _ a) a (IsPullback.of_hasPullback (I.subschemeι ≫ f) a).flip W]
  rfl

/-- If the closed subscheme cut out by `Ii` on the open `Ai : Vi ⟶ X`, intersected with a second
open `Aj : Vj ⟶ X`, lies in the closed subscheme cut out by `Ij` on `Vj`, then `Ij` is
contained in the restriction to `Vj` of the direct image of `Ii`. -/
theorem le_comap_map_of_inf_le {Vi Vj : Scheme.{u}} (Ai : Vi ⟶ X) [IsOpenImmersion Ai]
    (Aj : Vj ⟶ X) [IsOpenImmersion Aj] (Ii : Vi.IdealSheafData) (Ij : Vj.IdealSheafData)
    [QuasiCompact (Ii.subschemeι ≫ Ai)]
    (h : Subobject.mk (Ii.subschemeι ≫ Ai) ⊓ Subobject.mk Aj ≤
      Subobject.mk (Ij.subschemeι ≫ Aj)) :
    Ij ≤ (Ii.map Ai).comap Aj := by
  rw [comap_map_eq_ker_pullback_snd]
  have hf : (Subobject.mk (Ij.subschemeι ≫ Aj)).Factors
      (pullback.snd (Ii.subschemeι ≫ Ai) Aj ≫ Aj) := by
    refine Subobject.factors_of_le _ h ((Subobject.inf_factors _).2 ⟨?_, ?_⟩)
    · exact (Subobject.mk_factors_iff _ _).2
        ⟨pullback.fst (Ii.subschemeι ≫ Ai) Aj, pullback.condition⟩
    · exact (Subobject.mk_factors_iff _ _).2 ⟨pullback.snd (Ii.subschemeι ≫ Ai) Aj, rfl⟩
  obtain ⟨g₀, hg₀⟩ := (Subobject.mk_factors_iff _ _).1 hf
  let g : pullback (Ii.subschemeι ≫ Ai) Aj ⟶ Ij.subscheme := g₀
  have hg : g ≫ Ij.subschemeι ≫ Aj = pullback.snd (Ii.subschemeι ≫ Ai) Aj ≫ Aj := hg₀
  have hg' : g ≫ Ij.subschemeι = pullback.snd (Ii.subschemeι ≫ Ai) Aj :=
    (cancel_mono Aj).1 (by rw [Category.assoc]; exact hg)
  rw [← hg']
  calc Ij = Ij.subschemeι.ker := Ij.ker_subschemeι.symm
    _ ≤ (g ≫ Ij.subschemeι).ker := Hom.le_ker_comp g _

/-- A finite supremum of finite type ideal sheaves is of finite type. -/
theorem isFiniteType_iSup {ι : Type*} [Finite ι] (J : ι → X.IdealSheafData)
    (hJ : ∀ i, (J i).IsFiniteType) : (⨆ i, J i).IsFiniteType := by
  classical
  have := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup]
  refine Finset.sup_induction Stacks.FiniteTypeIdealSheaf.isFiniteType_bot
    (fun a ha b hb => ha.sup hb) fun i _ => hJ i

/-- The closed subscheme cut out by `J`, intersected with a subobject presented by a
monomorphism `a`, is the closed subscheme cut out by the restriction of `J` along `a`. -/
theorem inf_mk_eq_mk_comap {V : Scheme.{u}} (J : X.IdealSheafData) (a : V ⟶ X) [Mono a] :
    Subobject.mk J.subschemeι ⊓ Subobject.mk a = Subobject.mk ((J.comap a).subschemeι ≫ a) := by
  refine le_antisymm (Subobject.le_of_factors ?_) (le_inf ?_ ?_)
  · set P := Subobject.mk J.subschemeι ⊓ Subobject.mk a
    let u := (Subobject.mk J.subschemeι).factorThru P.arrow
      (Subobject.inf_arrow_factors_left _ _) ≫ (Subobject.underlyingIso J.subschemeι).hom
    let v := (Subobject.mk a).factorThru P.arrow
      (Subobject.inf_arrow_factors_right _ _) ≫ (Subobject.underlyingIso a).hom
    have hu : u ≫ J.subschemeι = P.arrow := by
      rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.factorThru_arrow]
    have hv : v ≫ a = P.arrow := by
      rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.factorThru_arrow]
    have key : (pullback.lift v u (hv.trans hu.symm) ≫ (J.comapIso a).inv) ≫
        (J.comap a).subschemeι ≫ a = P.arrow := by
      rw [Category.assoc, comapIso_inv_subschemeι_assoc, pullback.lift_fst_assoc, hv]
    exact (Subobject.mk_factors_iff _ _).2 ⟨_, key⟩
  · exact Subobject.mk_le_mk_of_comm ((J.comapIso a).hom ≫ pullback.snd a J.subschemeι)
      (by rw [Category.assoc, ← pullback.condition, comapIso_hom_fst_assoc])
  · exact Subobject.mk_le_mk_of_comm _ rfl

/-- Two monomorphisms defining the same subobject have the same kernel. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.ker_eq_of_mk_eq {Z₁ Z₂ : Scheme.{u}} {f : Z₁ ⟶ X}
    {g : Z₂ ⟶ X} [Mono f] [Mono g] (h : Subobject.mk f = Subobject.mk g) : f.ker = g.ker := by
  refine le_antisymm ?_ ?_
  · rw [← Subobject.ofMkLEMk_comp h.ge]; exact Hom.le_ker_comp _ _
  · rw [← Subobject.ofMkLEMk_comp h.le]; exact Hom.le_ker_comp _ _

variable [IsAffine X]

/-- **Finitely presented closed subschemes of finitely many quasi-compact opens of an affine
scheme, agreeing on overlaps, are cut out by one finite type ideal sheaf.**  Let `A i : V i ⟶ X`
be finitely many open immersions with quasi-compact sources and let `I i` be finite type ideal
sheaves on the `V i` whose closed subschemes agree on the overlaps, in the sense that
`V(I i) ∩ V j = V(I j) ∩ V i` as subobjects of `X`.  Then there is a finite type ideal sheaf
`J` on `X` restricting to `I i` on every `V i`.

The ideal sheaf `K = ⨅ i, (I i)_*` of functions vanishing on every `V(I i)` restricts to `I i`
on `V i`, by the compatibility; it is quasi-coherent but not of finite type, and the finitely
many generators of the `I i` over a finite affine cover of each `V i` are captured in a finite
type `J ≤ K` by `Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_forall_mem`. -/
@[ega "II 8.10.6" "special case"]
theorem exists_isFiniteType_comap_eq {ι : Type*} [Finite ι] {V : ι → Scheme.{u}}
    (A : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (A i)] [∀ i, CompactSpace (V i)]
    (I : ∀ i, (V i).IdealSheafData) (hI : ∀ i, (I i).IsFiniteType)
    (hcompat : ∀ i j, Subobject.mk ((I i).subschemeι ≫ A i) ⊓ Subobject.mk (A j) =
      Subobject.mk ((I j).subschemeι ≫ A j) ⊓ Subobject.mk (A i)) :
    ∃ J : X.IdealSheafData, J.IsFiniteType ∧ ∀ i, J.comap (A i) = I i := by
  classical
  set K : X.IdealSheafData := ⨅ i, (I i).map (A i) with hKdef
  have hK : ∀ j, K.comap (A j) = I j := by
    intro j
    refine le_antisymm ((comap_mono (A j) (iInf_le _ j)).trans (comap_map_le _ _)) ?_
    rw [hKdef, comap_iInf_of_isOpenImmersion]
    refine le_iInf fun i => le_comap_map_of_inf_le (A i) (A j) (I i) (I j) ?_
    rw [hcompat i j]
    exact inf_le_left
  have hcov : ∀ i, ∃ σ : Finset (V i).affineOpens,
      ⨆ w : σ, ((w.1 : (V i).affineOpens) : (V i).Opens) = ⊤ := fun i => by
    obtain ⟨σ, hσ⟩ := (TopologicalSpace.IsOpenCover.mk
      (iSup_affineOpens_eq_top (V i))).exists_finite_of_compactSpace
    exact ⟨σ, hσ.iSup_eq_top⟩
  choose σ hσ using hcov
  let W' : (i : ι) → σ i → X.affineOpens := fun i w =>
    ⟨A i ''ᵁ (w.1 : (V i).affineOpens), w.1.2.image_of_isOpenImmersion _⟩
  have hKfg : ∀ i (w : σ i), (K.ideal (W' i w)).FG := by
    intro i w
    have h2 : K.ideal (W' i w) = ((I i).ideal w.1).map
        ((A i).appIso (w.1 : (V i).affineOpens)).inv.hom := by
      rw [← hK i, ideal_comap_of_isOpenImmersion K (A i) w.1, Ideal.map_comap_of_surjective]
      exact (ConcreteCategory.bijective_of_isIso
        ((A i).appIso (w.1 : (V i).affineOpens)).inv).2
    rw [h2]
    exact (hI i w.1).map _
  have hcap : ∀ i (w : σ i), ∃ J : X.IdealSheafData, J.IsFiniteType ∧ J ≤ K ∧
      K.ideal (W' i w) ≤ J.ideal (W' i w) := by
    intro i w
    obtain ⟨s, hs⟩ := hKfg i w
    obtain ⟨J, hJft, hJK, hJs⟩ := Stacks.FiniteTypeIdealSheaf.exists_isFiniteType_le_forall_mem
      K (W' i w) s (fun x hx => hs ▸ Ideal.subset_span hx)
    refine ⟨J, hJft, hJK, ?_⟩
    rw [← hs, Ideal.span_le]
    exact hJs
  choose Jf hJfft hJfK hJfW using hcap
  refine ⟨⨆ p : (Σ i, σ i), Jf p.1 p.2, isFiniteType_iSup _ fun p => hJfft p.1 p.2, ?_⟩
  have hJK : (⨆ p : (Σ i, σ i), Jf p.1 p.2) ≤ K := iSup_le fun p => hJfK p.1 p.2
  intro i
  refine le_antisymm ((comap_mono (A i) hJK).trans (hK i).le) ?_
  rw [← hK i]
  refine le_of_iSup_eq_top (fun w : σ i => w.1) (hσ i) fun w => ?_
  rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion]
  refine Ideal.comap_mono ((hJfW i w).trans ?_)
  exact (le_iSup (fun p : (Σ i, σ i) => Jf p.1 p.2) ⟨i, w⟩) (W' i w)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SubschemePoints

variable {U₀ : BigFppfOver B S hS}

/-- The functor of points of an intersection of two subschemes is the intersection of their
functors of points. -/
theorem subschemePoints_inf (Z₁ Z₂ : Subobject ((BigFppfOver.toScheme B S hS).obj U₀)) :
    subschemePoints B S hS (Z₁ ⊓ Z₂) =
      subschemePoints B S hS Z₁ ⊓ subschemePoints B S hS Z₂ := by
  refine le_antisymm (fun T f hf => ?_) (fun T f hf => ?_)
  · have h := (Subobject.inf_factors _).1 ((mem_subschemePoints_iff B S hS f).1 hf)
    exact ⟨(mem_subschemePoints_iff B S hS f).2 h.1, (mem_subschemePoints_iff B S hS f).2 h.2⟩
  · exact (mem_subschemePoints_iff B S hS f).2 ((Subobject.inf_factors _).2
      ⟨(mem_subschemePoints_iff B S hS f).1 hf.1, (mem_subschemePoints_iff B S hS f).1 hf.2⟩)

/-- The functor of points of the subscheme presented by a morphism of the site with
monomorphic underlying morphism of schemes is the range of that morphism. -/
theorem subschemePoints_mk_eq_range {V : BigFppfOver B S hS} (i : V ⟶ U₀)
    [Mono ((BigFppfOver.toScheme B S hS).map i)] :
    subschemePoints B S hS (Subobject.mk ((BigFppfOver.toScheme B S hS).map i)) =
      Subfunctor.range (yoneda.map i) :=
  subschemePoints_eq_range B S hS i (Subobject.underlyingIso _).symm
    (Subobject.underlyingIso_arrow _)

end SubschemePoints

/-- An immersed subobject of a scheme is the arrow of an immersion. -/
private theorem isImmersion_arrow_mk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsImmersion f] :
    AlgebraicGeometry.IsImmersion (Subobject.mk f).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk f]
  infer_instance

/-- The intersection of an immersed subobject with an open subscheme is immersed. -/
private theorem isImmersion_arrow_inf {X : Scheme.{u}} (P O : Subobject X)
    (hP : AlgebraicGeometry.IsImmersion P.arrow) (hO : AlgebraicGeometry.IsOpenImmersion O.arrow) :
    AlgebraicGeometry.IsImmersion (P ⊓ O).arrow := by
  have hb : AlgebraicGeometry.IsOpenImmersion (Subobject.ofLE (P ⊓ O) P (by simp)) :=
    MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsOpenImmersion)
      (Subobject.inf_isPullback P O).flip hO
  rw [← Subobject.ofLE_arrow (h := (inf_le_left : P ⊓ O ≤ P))]
  infer_instance

/-- The arrow of the subobject of an open immersion is an open immersion. -/
private theorem isOpenImmersion_arrow_mk {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion f] :
    AlgebraicGeometry.IsOpenImmersion (Subobject.mk f).arrow := by
  rw [← Subobject.underlyingIso_hom_comp_eq_mk f]
  infer_instance

/-- An isomorphism of presheaves satisfies the inverse image of any property of morphisms of
schemes which respects isomorphisms and contains identities. -/
theorem inverseImage_presheaf_of_isIso (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : ∀ X : Scheme.{u}, P (𝟙 X)) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : F ⟶ G)
    [IsIso f] : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_of_isIso B S hS (MorphismProperty.RespectsIso.inverseImage _ _) (fun V => by
    show P ((BigFppfOver.toScheme B S hS).map (𝟙 V))
    rw [(BigFppfOver.toScheme B S hS).map_id]
    exact hP _) f

/-- For subspaces `T ≤ U` of `Y`, the preimage of `T` along `φ : yoneda.obj T₀ ⟶ Y` is the range
of the composite of the base change of `T ⊆ U` along the induced map to `U` with the base change
of `U ⊆ Y` along `φ`. -/
theorem preimage_eq_range_yoneda_map_of_le {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T₀ : BigFppfOver B S hS} {U T : Subfunctor Y} (hTU : T ≤ U) (φ : yoneda.obj T₀ ⟶ Y)
    (r : yoneda.relativelyRepresentable U.ι)
    (c : yoneda.relativelyRepresentable (T.preimage U.ι).ι) :
    T.preimage φ = Subfunctor.range (yoneda.map (c.snd (r.fst φ) ≫ r.snd φ)) := by
  refine le_antisymm (fun A g hg => ?_) (fun A g hg => ?_)
  · have hgU : g ∈ (U.preimage φ).obj A := hTU _ hg
    rw [← range_yoneda_snd_eq_preimage B S hS φ r] at hgU
    obtain ⟨h, rfl⟩ := hgU
    have hw := congrArg (fun m => m.app A h) (r.isPullback φ).w
    simp only [FunctorToTypes.comp] at hw
    have hhC : h ∈ ((T.preimage U.ι).preimage (r.fst φ)).obj A := by
      show (U.ι.app A ((r.fst φ).app A h)) ∈ T.obj A
      rw [hw]
      exact hg
    rw [← range_yoneda_snd_eq_preimage B S hS (r.fst φ) c] at hhC
    obtain ⟨k, rfl⟩ := hhC
    exact ⟨k, by simp [yoneda_map_app, Category.assoc]⟩
  · obtain ⟨k, rfl⟩ := hg
    have hk : (k : A.unop ⟶ c.pullback (r.fst φ)) ≫ c.snd (r.fst φ) ∈
        ((T.preimage U.ι).preimage (r.fst φ)).obj A := by
      rw [← range_yoneda_snd_eq_preimage B S hS (r.fst φ) c]
      exact ⟨k, rfl⟩
    have hw := congrArg (fun m => m.app A ((k : A.unop ⟶ c.pullback (r.fst φ)) ≫
      c.snd (r.fst φ))) (r.isPullback φ).w
    simp only [FunctorToTypes.comp] at hw
    show (φ.app A ((yoneda.map (c.snd (r.fst φ) ≫ r.snd φ)).app A k)) ∈ T.obj A
    have hk' : U.ι.app A ((r.fst φ).app A ((k : A.unop ⟶ c.pullback (r.fst φ)) ≫
        c.snd (r.fst φ))) ∈ T.obj A := hk
    rw [hw] at hk'
    simpa [yoneda_map_app, Category.assoc] using hk'

/-- A quasi-compact open subspace `U` of `Y` and a finitely presented closed subspace `T` of `U`,
read along an isomorphism `φ : yoneda.obj T₀ ⟶ Y`: on functors of points, `U` is a quasi-compact
open subscheme `A : V ⟶ X₀` of the scheme `X₀` of `T₀`, and `T` the closed subscheme of `V` cut
out by a finite type ideal sheaf `I`. -/
theorem exists_isFiniteType_preimage_eq_subschemePoints {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T₀ : BigFppfOver B S hS} (φ : yoneda.obj T₀ ⟶ Y) [IsIso φ] {U T : Subfunctor Y}
    (hU : IsOpenSubspace B S hS U) (hUqc : IsQuasiCompactSpace B S hS U.toFunctor) (hTU : T ≤ U)
    (hTc : IsClosedSubspace B S hS (T.preimage U.ι))
    (hTf : IsFinitePresentation B S hS (T.preimage U.ι).ι) :
    ∃ (V : Scheme.{u}) (A : V ⟶ (BigFppfOver.toScheme B S hS).obj T₀)
      (_ : AlgebraicGeometry.IsOpenImmersion A) (_ : CompactSpace V) (I : V.IdealSheafData),
      I.IsFiniteType ∧ U.preimage φ = subschemePoints B S hS (Subobject.mk A) ∧
        T.preimage φ = subschemePoints B S hS (Subobject.mk (I.subschemeι ≫ A)) := by
  let F := BigFppfOver.toScheme B S hS
  let r := hU.2.rep
  let b := r.fst φ
  let c := hTc.2.rep
  have : AlgebraicGeometry.IsOpenImmersion (F.map (r.snd φ)) := hU.2.property_snd φ
  have : IsIso b := (r.isPullback φ).isIso_fst_of_isIso
  have : AlgebraicGeometry.IsClosedImmersion (F.map (c.snd b)) := hTc.2.property_snd b
  have : CompactSpace (F.obj (r.pullback φ)) := compactSpace_of_isQuasiCompactSpace_yoneda_obj
    B S hS (isQuasiCompactSpace_of_iso B S hS (asIso b).symm hUqc)
  have hfg : (F.map (c.snd b)).ker.IsFiniteType := fun A =>
    fg_ideal_ker_rep_snd_of_isFinitePresentation B S hS
      (Z := ⟨(T.preimage U.ι).toFunctor, hTc.1⟩) (X := ⟨U.toFunctor, hU.1⟩)
      (ObjectProperty.homMk (T.preimage U.ι).ι) hTc.2 hTf
      (inverseImage_presheaf_of_isIso B S hS (@Etale.{u}) (fun _ => inferInstance) b) A
  have : Mono (F.map (c.snd b ≫ r.snd φ)) := by
    rw [F.map_comp]
    infer_instance
  have hmk : Subobject.mk ((F.map (c.snd b)).ker.subschemeι ≫ F.map (r.snd φ)) =
      Subobject.mk (F.map (c.snd b ≫ r.snd φ)) :=
    (Subobject.mk_eq_mk_of_comm _ _ (asIso (F.map (c.snd b)).toImage)
      (by rw [asIso_hom, ← Category.assoc, Scheme.Hom.toImage_imageι, F.map_comp])).symm
  refine ⟨_, F.map (r.snd φ), inferInstance, inferInstance, _, hfg, ?_, ?_⟩
  · rw [subschemePoints_mk_eq_range]
    exact (range_yoneda_snd_eq_preimage B S hS φ r).symm
  · rw [hmk, subschemePoints_mk_eq_range]
    exact preimage_eq_range_yoneda_map_of_le B S hS hTU φ r c

/-- Read along an isomorphism `e : Y ≅ yoneda.obj T₀` of an algebraic space, with `X₀` the scheme
of `T₀`, a finite type ideal sheaf `J` on `X₀` restricting to `I i` on open subschemes `A i` of
`X₀` cuts out a finitely presented closed subspace `T'` of `Y` with `T' ⊓ U i = T i`, where
`U i` and `T i` are the subspaces of `Y` whose functors of points on `X₀` are those of `A i` and
of the closed subscheme cut out by `I i`. -/
theorem exists_closedSubspace_of_isFiniteType {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {T₀ : BigFppfOver B S hS} (e : Y ≅ yoneda.obj T₀)
    {J : ((BigFppfOver.toScheme B S hS).obj T₀).IdealSheafData} (hJ : J.IsFiniteType)
    {ι : Type*} (U T : ι → Subfunctor Y) {V : ι → Scheme.{u}}
    (A : ∀ i, V i ⟶ (BigFppfOver.toScheme B S hS).obj T₀)
    [∀ i, AlgebraicGeometry.IsOpenImmersion (A i)] (I : ∀ i, (V i).IdealSheafData)
    (hJI : ∀ i, J.comap (A i) = I i)
    (hUpts : ∀ i, (U i).preimage e.inv = subschemePoints B S hS (Subobject.mk (A i)))
    (hTpts : ∀ i, (T i).preimage e.inv =
      subschemePoints B S hS (Subobject.mk ((I i).subschemeι ≫ A i))) :
    ∃ T' : Subfunctor Y, IsClosedSubspace B S hS T' ∧ IsFinitePresentation B S hS T'.ι ∧
      ∀ i, T' ⊓ U i = T i := by
  let F := BigFppfOver.toScheme B S hS
  let Z : Subobject (F.obj T₀) := Subobject.mk J.subschemeι
  have hZci : AlgebraicGeometry.IsClosedImmersion Z.arrow := by
    rw [← Subobject.underlyingIso_hom_comp_eq_mk]
    infer_instance
  have hZimm : AlgebraicGeometry.IsImmersion Z.arrow := inferInstance
  let T'₀ := subschemePoints B S hS Z
  have hT'₀ : T'₀ = Subfunctor.range (yoneda.map (subschemeι B S hS Z hZimm)) :=
    subschemePoints_eq_range B S hS _ (Iso.refl _) (Category.id_comp _)
  have hT'₀c : IsClosedSubspace B S hS T'₀ := by
    rw [hT'₀]
    exact isClosedSubspace_range_yoneda_map B S hS _ hZci
  let T' := T'₀.preimage e.hom
  have hT'φ : T'.preimage e.inv = T'₀ := by
    simp only [T', ← Subfunctor.preimage_comp, e.inv_hom_id, Subfunctor.preimage_id]
  have hpb := Subfunctor.isPullback_preimage e.hom T'₀
  have hT'c : IsClosedSubspace B S hS T' := by
    have : IsIso (T'₀.fromPreimage e.hom) := hpb.isIso_fst_of_isIso
    exact ⟨isAlgebraicSpace_of_iso B S hS (asIso (T'₀.fromPreimage e.hom)).symm hT'₀c.1,
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hpb hT'₀c.2⟩
  refine ⟨T', hT'c, ?_, fun i => ?_⟩
  · refine (isFinitePresentation_iff_fg_ker_of_surjectiveEtaleChart B S hS
      (Z := ⟨T'.toFunctor, hT'c.1⟩) (X := ⟨Y, hY⟩) (ObjectProperty.homMk T'.ι) hT'c.2
      (inverseImage_presheaf_of_isIso B S hS (@Etale.{u}) (fun _ => inferInstance) e.inv)
      (inverseImage_presheaf_of_isIso B S hS (@Surjective.{u}) (fun _ => inferInstance)
        e.inv)).2 fun A' => ?_
    have hci : AlgebraicGeometry.IsClosedImmersion (F.map (hT'c.2.rep.snd e.inv)) :=
      hT'c.2.property_snd e.inv
    have hmk : Subobject.mk (F.map (hT'c.2.rep.snd e.inv)) = Z := by
      refine subschemePoints_injective B S hS (isImmersion_arrow_mk _) hZimm ?_
      rw [subschemePoints_mk_eq_range, range_yoneda_snd_eq_preimage B S hS e.inv hT'c.2.rep,
        hT'φ]
    show ((F.map (hT'c.2.rep.snd e.inv)).ker.ideal A').FG
    rw [(Scheme.Hom.ker_eq_of_mk_eq hmk).trans J.ker_subschemeι]
    exact hJ A'
  · have h : (T' ⊓ U i).preimage e.inv = (T i).preimage e.inv := by
      show T'.preimage e.inv ⊓ (U i).preimage e.inv = _
      rw [hT'φ, hUpts, hTpts, ← subschemePoints_inf]
      congr 1
      rw [← hJI i]
      exact Scheme.IdealSheafData.inf_mk_eq_mk_comap J (A i)
    simpa only [← Subfunctor.preimage_comp, e.hom_inv_id, Subfunctor.preimage_id] using
      congrArg (fun Z : Subfunctor (yoneda.obj T₀) => Z.preimage e.hom) h

/-- **The affine case of extending finitely presented closed subspaces.**  Let `Y` be an affine
algebraic space, let `U i` be finitely many quasi-compact open subspaces of `Y`, and let `T i`
be a closed subspace of `U i` whose closed immersion into `U i` is of finite presentation, the
`T i` agreeing on the overlaps: `T i ∩ U j = T j ∩ U i`.  Then there is a closed subspace `T'`
of `Y`, of finite presentation, with `T' ∩ U i = T i` for every `i`.

Writing `Y` as the functor of points of an affine scheme `X₀` of the site, everything is read
on `X₀`: the `U i` become quasi-compact opens `V i ⊆ X₀`, the `T i` finite type ideal sheaves on
them, and the statement is
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isFiniteType_comap_eq`.  The closed subspace
`T'` is the subspace cut out by the resulting ideal sheaf `J` along the chart `X₀ ≅ Y`, and it
is compared with the `T i` through their functors of points on `X₀`. -/
theorem exists_closedSubspace_extension_of_isAffineSpace
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYa : IsAffineSpace B S hS Y)
    {ι : Type} [Finite ι] (U : ι → Subfunctor Y) (hU : ∀ i, IsOpenSubspace B S hS (U i))
    (hUqc : ∀ i, IsQuasiCompactSpace B S hS (U i).toFunctor)
    (T : ι → Subfunctor Y) (hTU : ∀ i, T i ≤ U i)
    (hTc : ∀ i, IsClosedSubspace B S hS ((T i).preimage (U i).ι))
    (hTf : ∀ i, IsFinitePresentation B S hS ((T i).preimage (U i).ι).ι)
    (hcompat : ∀ i j, T i ⊓ U j = T j ⊓ U i) :
    ∃ T' : Subfunctor Y, IsClosedSubspace B S hS T' ∧ IsFinitePresentation B S hS T'.ι ∧
      ∀ i, T' ⊓ U i = T i := by
  obtain ⟨T₀, hT₀, ⟨e⟩⟩ := hYa
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀) := hT₀
  choose V A hA hV I hI hUpts hTpts using fun i =>
    exists_isFiniteType_preimage_eq_subschemePoints B S hS e.inv (hU i) (hUqc i) (hTU i) (hTc i)
      (hTf i)
  have hcompat₀ : ∀ i j, Subobject.mk ((I i).subschemeι ≫ A i) ⊓ Subobject.mk (A j) =
      Subobject.mk ((I j).subschemeι ≫ A j) ⊓ Subobject.mk (A i) := by
    intro i j
    refine subschemePoints_injective B S hS
      (isImmersion_arrow_inf _ _ (isImmersion_arrow_mk _) (isOpenImmersion_arrow_mk _))
      (isImmersion_arrow_inf _ _ (isImmersion_arrow_mk _) (isOpenImmersion_arrow_mk _)) ?_
    rw [subschemePoints_inf, subschemePoints_inf, ← hTpts, ← hUpts, ← hTpts, ← hUpts]
    exact congrArg (Subfunctor.preimage · e.inv) (hcompat i j)
  obtain ⟨J, hJft, hJ⟩ := Scheme.IdealSheafData.exists_isFiniteType_comap_eq A I hI hcompat₀
  exact exists_closedSubspace_of_isFiniteType B S hS hY e hJft U T A I hJ hUpts hTpts

end AlgebraicGeometry.Space
