module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedChartLocality
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableOverAffineSetCondition

/-!
# Sheaves representable étale over a formal algebraic space

Let `S` be a scheme of a big fppf site. The étale case of **Stacks 0AJH** says that a sheaf `X`
with a morphism `X ⟶ Y`, representable by algebraic spaces and étale, to an *affine* formal
algebraic space `Y` is a formal algebraic space, provided `X` satisfies the set-theoretic
condition of Stacks 0AIS. This file records that statement as
`AlgebraicGeometry.FormalSpace.RepresentableEtaleOverAffineIsFormal` and derives from it
everything the proof of **Stacks 0ANG** needs about fibre products, so that the proof no longer
runs through the general colimit statement of Stacks 0AIU.

* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_isRepresentableEtale_over_formal`:
  the same over an arbitrary formal algebraic space `Y`, through an atlas of `Y` (Stacks 0AJ1).
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart_of_etale`: Stacks 0AJ3
  for the fibre product `V ×_Y X` of a morphism of formal algebraic spaces with a chart of its
  target, with no set-theoretic condition assumed.
* `AlgebraicGeometry.FormalSpace.hasFormalAffineChartPullbacks_of_etale`: Stacks 0AJ2 in the
  shape the proof of Stacks 0AKX consumes.
* `AlgebraicGeometry.FormalSpace.hasEtaleRefinementOfSourceCover_of_etale`: the covering
  refinement of the proof of Stacks 0ANG.

Every fibre product formed in these arguments lies over an affine formal algebraic space by a
base change of a representable étale morphism, which is why the étale case of Stacks 0AJH is
enough.

## References

* [Stacks Project, Tag 0AJ1](https://stacks.math.columbia.edu/tag/0AJ1)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AJH](https://stacks.math.columbia.edu/tag/0AJH)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The étale case of Stacks 0AJH**: a sheaf which is representable by algebraic spaces and
étale over an affine formal algebraic space is a formal algebraic space. -/
abbrev RepresentableEtaleOverAffineIsFormal : Prop :=
  ∀ {X Y : FppfSheaf B S hS} (f : X ⟶ Y), IsAffineFormalAlgebraicSpace B S hS Y →
    IsRepresentableEtale B S hS f → IsFormalAlgebraicSpace B S hS X

/-- **Stacks 0AJ1 over a formal algebraic space.** From the étale case of Stacks 0AJH over an
affine base: a sheaf satisfying the set-theoretic condition of Stacks 0AIS which is
representable étale over a formal algebraic space `Y` is a formal algebraic space. Its base
changes to the charts of an atlas of `Y` are formal algebraic spaces by the affine case, and
they form an étale covering of it. -/
theorem isFormalAlgebraicSpace_of_isRepresentableEtale_over_formal
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsRepresentableEtale B S hS f) (hXset : SatisfiesSetTheoreticCondition B S hS X) :
    IsFormalAlgebraicSpace B S hS X := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, I, V, v, hVaffine, hVetale, hVsurj⟩ := hY
  exact isFormalAlgebraicSpace_of_etaleCover B S hS X (fun i ↦ pullback (v i) f)
    (fun i ↦ pullback.snd (v i) f)
    (fun i ↦ hEt (pullback.fst (v i) f) (hVaffine i)
      (isRepresentableEtale_pullback_fst B S hS (v i) f hf))
    (fun i ↦ isRepresentableEtale_pullback_snd B S hS (v i) f (hVetale i))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd f v hVsurj) hXset

/-- **Stacks 0AJ3** for a fibre product of two affine formal algebraic spaces over a formal
algebraic space, one of whose legs is representable étale, from the étale case of Stacks 0AJH:
the projection to the other leg is a base change of the representable étale one. No instance
of the set-theoretic condition of Stacks 0AIS, and no hypothesis on the base, is assumed. -/
theorem isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y V : FppfSheaf B S hS} (v : V ⟶ Y) (f : X ⟶ Y)
    (hX : IsAffineFormalAlgebraicSpace B S hS X) (hv : IsRepresentableEtale B S hS v) :
    IsFormalAlgebraicSpace B S hS (pullback v f) :=
  hEt (pullback.snd v f) hX (isRepresentableEtale_pullback_snd B S hS v f hv)

/-- **Stacks 0AJ3** for the fibre product `V ×_Y X` of a morphism of formal algebraic spaces
with an affine formal chart of its target, from the étale case of Stacks 0AJH, with no instance
of the set-theoretic condition of Stacks 0AIS assumed. This is
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_pullback_chart` without its input
Stacks 0AIU. -/
theorem isFormalAlgebraicSpace_pullback_chart_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y : FppfSheaf B S hS} {f : X ⟶ Y}
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (V : FppfSheaf B S hS) (v : V ⟶ Y) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hv : IsRepresentableEtale B S hS v) :
    IsFormalAlgebraicSpace B S hS (pullback v f) :=
  isFormalAlgebraicSpace_of_isRepresentableEtale_over_formal B S hS hEt
    (pullback.snd v f) hX (isRepresentableEtale_pullback_snd B S hS v f hv)
    (satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS v f
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS hV)
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX) hV.1 hX.1)

/-- **Stacks 0AJ2 in the shape the proof of Stacks 0AKX consumes**, from the étale case of
Stacks 0AJH: the fibre product of an affine étale chart `v : V ⟶ T` of a sheaf with a
representable étale morphism `f : U ⟶ T` from an affine formal algebraic space is a formal
algebraic space: the projection to `U` is a base change of `v`, hence representable étale over
the affine formal algebraic space `U`. -/
theorem hasFormalAffineChartPullbacks_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS) :
    HasFormalAffineChartPullbacks B S hS :=
  fun f hU _ _ v _ hv ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal B S hS hEt v f hU hv

/-! ### The covering refinement in the proof of Stacks 0ANG -/

/-- The refinement of a covering constructed in the proof of **Stacks 0ANG**, before the finite
subfamily is extracted, from the étale case of Stacks 0AJH. This is
`AlgebraicGeometry.FormalSpace.exists_affineEtaleCover_refining_sourceCover` without its input
Stacks 0AIU, and without its hypotheses that `X` and `Y` be formal algebraic spaces: each of the
three fibre products formed lies over an affine formal algebraic space by a base change of a
representable étale morphism. -/
theorem exists_affineEtaleCover_refining_sourceCover_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    {I : Type (u + 1)} (U V : I → FppfSheaf B S hS) (u : ∀ i, U i ⟶ X) (v : ∀ i, V i ⟶ Y)
    (t : ∀ i, U i ⟶ V i) (hUcover : IsAffineEtaleCover B S hS U u)
    (_hVaffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (V i))
    (hVetale : ∀ i, IsRepresentableEtale B S hS (v i))
    (hVsquare : ∀ i, u i ≫ f = t i ≫ v i)
    (U₀ V₀ : FppfSheaf B S hS) (a : U₀ ⟶ X) (b : V₀ ⟶ Y) (τ : U₀ ⟶ V₀)
    (hU₀ : IsAffineFormalAlgebraicSpace B S hS U₀)
    (hV₀ : IsAffineFormalAlgebraicSpace B S hS V₀)
    (ha : IsRepresentableEtale B S hS a) (hb : IsRepresentableEtale B S hS b)
    (hsquare : a ≫ f = τ ≫ b) :
    ∃ (σ : Type (u + 1)) (k : σ → I) (W Z : σ → FppfSheaf B S hS)
      (p : ∀ s, W s ⟶ U₀) (q : ∀ s, W s ⟶ U (k s)) (m : ∀ s, W s ⟶ Z s)
      (r : ∀ s, Z s ⟶ V (k s)) (c : ∀ s, Z s ⟶ V₀),
      IsAffineEtaleCover B S hS W p ∧ (∀ s, IsAffineFormalAlgebraicSpace B S hS (Z s)) ∧
        (∀ s, IsRepresentableEtale B S hS (q s)) ∧
        (∀ s, IsRepresentableEtale B S hS (r s)) ∧
        (∀ s, IsRepresentableEtale B S hS (c s)) ∧
        (∀ s, q s ≫ t (k s) = m s ≫ r s) ∧ ∀ s, p s ≫ τ = m s ≫ c s := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hUaffine, hUetale, hUsurj⟩ := hUcover
  -- `Qᵢ = Vᵢ ×_Y V₀` and `Nᵢ = Uᵢ ×_X U₀` are formal algebraic spaces
  have hQ : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (v i) b) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal B S hS hEt (v i) b
      hV₀ (hVetale i)
  have hN : ∀ i, IsFormalAlgebraicSpace B S hS (pullback (u i) a) := fun i ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal B S hS hEt (u i) a
      hU₀ (hUetale i)
  -- the morphism `gᵢ : Nᵢ ⟶ Qᵢ` induced by `Uᵢ ⟶ Vᵢ` and `U₀ ⟶ V₀`
  obtain ⟨g, hgfst, hgsnd⟩ : ∃ g : ∀ i, pullback (u i) a ⟶ pullback (v i) b,
      (∀ i, g i ≫ pullback.fst (v i) b = pullback.fst (u i) a ≫ t i) ∧
        ∀ i, g i ≫ pullback.snd (v i) b = pullback.snd (u i) a ≫ τ := by
    refine ⟨fun i ↦ pullback.lift (pullback.fst (u i) a ≫ t i) (pullback.snd (u i) a ≫ τ) ?_,
      fun i ↦ pullback.lift_fst _ _ _, fun i ↦ pullback.lift_snd _ _ _⟩
    rw [Category.assoc, Category.assoc, ← hVsquare i, ← hsquare, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  -- coverings `{Zᵢⱼ ⟶ Qᵢ}` of the fibre products `Qᵢ` and `{Mᵢₗ ⟶ Nᵢ}` of the `Nᵢ`
  choose J Z z hZaffine hZetale hZsurj using fun i ↦ (hQ i).2
  choose L M ml hMaffine hMetale hMsurj using fun i ↦ (hN i).2
  -- `Tᵢⱼₗ = Zᵢⱼ ×_{Qᵢ} Mᵢₗ` is a formal algebraic space, both its legs being affine
  have hT : ∀ i (l : L i) (j : J i),
      IsFormalAlgebraicSpace B S hS (pullback (z i j) (ml i l ≫ g i)) := fun i l j ↦
    isFormalAlgebraicSpace_pullback_of_isRepresentableEtale_of_isAffineFormal B S hS hEt (z i j)
      (ml i l ≫ g i) (hMaffine i l) (hZetale i j)
  -- coverings `{Wᵢⱼₗₖ ⟶ Tᵢⱼₗ}`
  choose K W w hWaffine hWetale hWsurj using fun (i : I) (l : L i) (j : J i) ↦ (hT i l j).2
  -- the composite family `{Wᵢⱼₗₖ ⟶ U₀}` is an affine étale covering of `U₀`
  have hcover : IsAffineEtaleCover B S hS
      (fun s : (i : I) × ((l : L i) × ((j : J i) × K i l j)) ↦
        W s.1 s.2.1 s.2.2.1 s.2.2.2)
      (fun s ↦ ((w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
          pullback.snd (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1)) ≫ ml s.1 s.2.1) ≫
        pullback.snd (u s.1) a) := by
    refine ⟨fun s ↦ hWaffine s.1 s.2.1 s.2.2.1 s.2.2.2, fun s ↦ IsRepresentableEtale.comp B S hS
      (IsRepresentableEtale.comp B S hS
        (IsRepresentableEtale.comp B S hS (hWetale s.1 s.2.1 s.2.2.1 s.2.2.2)
          (isRepresentableEtale_pullback_snd B S hS (z s.1 s.2.2.1)
            (ml s.1 s.2.1 ≫ g s.1) (hZetale s.1 s.2.2.1)))
        (hMetale s.1 s.2.1))
      (isRepresentableEtale_pullback_snd B S hS (u s.1) a (hUetale s.1)), ?_⟩
    refine Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (fun i ↦ pullback.snd (u i) a)
      (fun i (p : (l : L i) × ((j : J i) × K i l j)) ↦
        (w i p.1 p.2.1 p.2.2 ≫ pullback.snd (z i p.2.1) (ml i p.1 ≫ g i)) ≫ ml i p.1)
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd a u hUsurj) fun i ↦ ?_
    refine Sheaf.isLocallySurjective_sigmaDesc_sigma_comp (ml i)
      (fun l (p : (j : J i) × K i l j) ↦
        w i l p.1 p.2 ≫ pullback.snd (z i p.1) (ml i l ≫ g i)) (hMsurj i) fun l ↦ ?_
    exact Sheaf.isLocallySurjective_sigmaDesc_sigma_comp
      (fun j ↦ pullback.snd (z i j) (ml i l ≫ g i)) (w i l)
      (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (ml i l ≫ g i) (z i) (hZsurj i))
      (hWsurj i l)
  refine ⟨(i : I) × ((l : L i) × ((j : J i) × K i l j)), fun s ↦ s.1,
    fun s ↦ W s.1 s.2.1 s.2.2.1 s.2.2.2, fun s ↦ Z s.1 s.2.2.1,
    fun s ↦ ((w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
        pullback.snd (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1)) ≫ ml s.1 s.2.1) ≫
      pullback.snd (u s.1) a,
    fun s ↦ ((w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
        pullback.snd (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1)) ≫ ml s.1 s.2.1) ≫
      pullback.fst (u s.1) a,
    fun s ↦ w s.1 s.2.1 s.2.2.1 s.2.2.2 ≫
      pullback.fst (z s.1 s.2.2.1) (ml s.1 s.2.1 ≫ g s.1),
    fun s ↦ z s.1 s.2.2.1 ≫ pullback.fst (v s.1) b,
    fun s ↦ z s.1 s.2.2.1 ≫ pullback.snd (v s.1) b, hcover,
    fun s ↦ hZaffine s.1 s.2.2.1, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_⟩
  · exact IsRepresentableEtale.comp B S hS
      (IsRepresentableEtale.comp B S hS
        (IsRepresentableEtale.comp B S hS (hWetale s.1 s.2.1 s.2.2.1 s.2.2.2)
          (isRepresentableEtale_pullback_snd B S hS (z s.1 s.2.2.1)
            (ml s.1 s.2.1 ≫ g s.1) (hZetale s.1 s.2.2.1)))
        (hMetale s.1 s.2.1))
      (isRepresentableEtale_pullback_fst B S hS (u s.1) a ha)
  · exact IsRepresentableEtale.comp B S hS (hZetale s.1 s.2.2.1)
      (isRepresentableEtale_pullback_fst B S hS (v s.1) b hb)
  · exact IsRepresentableEtale.comp B S hS (hZetale s.1 s.2.2.1)
      (isRepresentableEtale_pullback_snd B S hS (v s.1) b (hVetale s.1))
  · simp only [Category.assoc, ← hgfst s.1, pullback.condition_assoc]
  · simp only [Category.assoc, ← hgsnd s.1, pullback.condition_assoc]

/-- **The covering refinement in the proof of Stacks 0ANG**, from the étale case of
Stacks 0AJH: `AlgebraicGeometry.FormalSpace.hasEtaleRefinementOfSourceCover` without its input
Stacks 0AIU, and for an arbitrary morphism of fppf sheaves. -/
theorem hasEtaleRefinementOfSourceCover_of_etale
    (hEt : RepresentableEtaleOverAffineIsFormal B S hS)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) :
    HasEtaleRefinementOfSourceCover B S hS f := by
  intro I U V u v t hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ', k, W, Z, p, q, m, r, c, hWcover, hZaff, hq, hr, hc, hsq₁, hsq₂⟩ :=
    exists_affineEtaleCover_refining_sourceCover_of_etale B S hS hEt f U V u v t
      hUcover hVaffine hVetale hVsquare U₀ V₀ a b τ hU₀ hV₀ ha hb hsquare
  obtain ⟨σ, hσ, κ, hsub⟩ :=
    exists_finite_subcover_of_isAffineFormalAlgebraicSpace B S hS U₀ W p hU₀ hWcover
  exact ⟨σ, hσ, fun s ↦ k (κ s), fun s ↦ W (κ s), fun s ↦ Z (κ s), fun s ↦ p (κ s),
    fun s ↦ q (κ s), fun s ↦ m (κ s), fun s ↦ r (κ s), fun s ↦ c (κ s), hsub,
    fun s ↦ hZaff (κ s), fun s ↦ hq (κ s), fun s ↦ hr (κ s), fun s ↦ hc (κ s),
    fun s ↦ hsq₁ (κ s), fun s ↦ hsq₂ (κ s)⟩

end AlgebraicGeometry.FormalSpace

end
