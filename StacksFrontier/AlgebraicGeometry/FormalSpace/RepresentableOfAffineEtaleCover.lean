module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SchemeAtlas

/-!
# Representability by algebraic spaces from an affine étale covering of the source

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S`. If `{Uᵢ ⟶ X}` is a covering as in Definition 0AIM such that every
composite `Uᵢ ⟶ X ⟶ Y` is representable by algebraic spaces, then `f` is representable by
algebraic spaces.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isAffineEtaleCover_of_isAlgebraicSpaceULift`: an fppf
  sheaf which is an algebraic space admits a covering as in Definition 0AIM by sheaves
  represented by affine objects of the site.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_uliftYoneda`: a sheaf represented by an
  object of the site is a formal algebraic space.
* `AlgebraicGeometry.FormalSpace.isRepresentable_of_affineEtaleCover_of_isRepresentable_comp`:
  the result described above.

## Implementation notes

Fix a point `ξ : T ⟶ Y` with `T` an object of the site and put `P = T ×_Y X`. Each base change
`Pᵢ = P ×_X Uᵢ ≅ T ×_Y Uᵢ` is an algebraic space, because `Uᵢ ⟶ Y` is representable by
algebraic spaces, so it is covered by the sheaves represented by the affine opens of a scheme
atlas. Composing with the representable étale projections `Pᵢ ⟶ P` gives a jointly surjective
family of representable étale maps to `P` out of affine schemes. The set-theoretic condition of
Stacks 0AIS holds for `P` because it holds for the fibre product of two sheaves with
representable relative products over a third (Stacks 0AIP supplies these for `X`, `Y` and the
sheaf represented by `T`), so `P` is a formal algebraic space, and Stacks 0AIS, observation (2),
makes it an algebraic space.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AN4](https://stacks.math.columbia.edu/tag/0AN4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of fppf sheaves which is étale relative to the universe-lifted Yoneda embedding,
that is representable by objects of the site with étale represented base changes, is
representable étale. -/
theorem isRepresentableEtale_of_relative_etale {F G : FppfSheaf B S hS} (f : F ⟶ G)
    (hf : (Space.etaleOnSite B S hS).relative (uliftYoneda.{u + 1}) f.hom) :
    IsRepresentableEtale B S hS f := by
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.etaleOnSite B S hS)
  exact ⟨fun U ξ ↦ Space.isAlgebraicSpaceULift_of_iso B S hS
    ((hf.rep.isPullback ξ).isoPullback ≪≫ pullbackSymmetry _ _)
    (Space.isAlgebraicSpaceULift_uliftYoneda B S hS _), fun U ξ V φ hφ ↦
    MorphismProperty.comp_mem _ _ _ hφ
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback ξ f.hom).flip hf)⟩

/-- The sheaf represented by an object of the site satisfies the set-theoretic condition of
Stacks 0AIS: it is its own representable surjection, and so is its kernel pair. -/
private theorem satisfiesSetTheoreticCondition_uliftYoneda_aux (T : BigFppfOver B S hS) :
    SatisfiesSetTheoreticCondition B S hS
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T) := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let X := J.uliftYoneda.{u + 1}.obj T
  let eX : X.obj ≅ uliftYoneda.{u + 1}.obj T := J.uliftYonedaCompSheafToPresheaf.app _
  exact ⟨T, T, X, X, ⟨eX⟩, ⟨eX⟩, 𝟙 X, inferInstance,
    (asIso (pullback.fst (𝟙 X) (𝟙 X))).inv, inferInstance⟩

/-- The sheaf represented by an affine object of the site is an affine formal algebraic space:
it is the colimit of the constant one-stage diagram at that object. -/
theorem isAffineFormalAlgebraicSpace_uliftYoneda (V : BigAffineFppf B S hS) :
    IsAffineFormalAlgebraicSpace B S hS
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
        ((BigAffineFppf.inclusion B S hS).obj V)) := by
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let F := BigAffineFppf.inclusion B S hS ⋙ Sheaf.sheafifiedYoneda J
  refine ⟨satisfiesSetTheoreticCondition_uliftYoneda_aux B S hS _,
    PUnit.{u + 2}, inferInstance, inferInstance, inferInstance,
    (Functor.const PUnit.{u + 2}).obj V, fun _ _ _ ↦ ?_, ⟨?_⟩⟩
  · exact ⟨inferInstance, Scheme.Hom.surjective _⟩
  · exact ((Sheaf.sheafifiedYonedaIsoUliftYoneda' J).app _).symm ≪≫
      IsColimit.coconePointUniqueUpToIso (isColimitConstCocone PUnit.{u + 2} (F.obj V))
        (colimit.isColimit _) ≪≫ HasColimit.isoOfNatIso (Functor.constComp _ V F).symm

/-- **An algebraic space has an affine étale covering.** An fppf sheaf on the big fppf site of
`S` which is an algebraic space admits a covering as in Definition 0AIM whose members are
sheaves represented by affine objects of the site: the affine opens of a scheme atlas. -/
theorem exists_isAffineEtaleCover_of_isAlgebraicSpaceULift (Z : FppfSheaf B S hS)
    (hZ : Space.IsAlgebraicSpaceULift.{u + 1} B S hS Z.obj) :
    ∃ (K : Type (u + 1)) (V : K → BigAffineFppf B S hS)
      (a : ∀ k, (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj
        ((BigAffineFppf.inclusion B S hS).obj (V k)) ⟶ Z),
      IsAffineEtaleCover B S hS _ a := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  have _ := MorphismProperty.relative_isStableUnderBaseChange
    (F := uliftYoneda.{u + 1} (C := BigFppfOver B S hS)) (Space.etaleOnSite B S hS)
  obtain ⟨W, q, hqs, hqe⟩ := hZ.exists_atlas
  let 𝒰 := W.left.obj.affineCover
  let V₀ (i : 𝒰.I₀) : B.Schemes :=
    ⟨𝒰.X i, Scheme.size_lt_of_isOpenImmersion (𝒰.f i) W.left.property⟩
  let a₀ (i : 𝒰.I₀) : V₀ i ⟶ W.left := ObjectProperty.homMk (𝒰.f i)
  let V (i : 𝒰.I₀) : BigAffineFppf B S hS :=
    ⟨Over.mk (a₀ i ≫ W.hom), inferInstanceAs (IsAffine (𝒰.X i))⟩
  let a (i : 𝒰.I₀) : (BigAffineFppf.inclusion B S hS).obj (V i) ⟶ W := Over.homMk (a₀ i)
  let qS : J.uliftYoneda.{u + 1}.obj W ⟶ Z := ⟨q⟩
  refine ⟨ULift.{u + 1} 𝒰.I₀, fun k ↦ V k.down, fun k ↦ J.uliftYoneda.{u + 1}.map (a k.down) ≫ qS,
    fun k ↦ isAffineFormalAlgebraicSpace_uliftYoneda B S hS (V k.down), fun k ↦ ?_, ?_⟩
  · exact isRepresentableEtale_of_relative_etale B S hS _ (MorphismProperty.comp_mem _ _ _
      (Space.relative_uliftYoneda_map B S hS _ (a k.down)
        (inferInstanceAs (Etale (𝒰.f k.down)))) hqe)
  · -- the affine opens cover `W`, and the atlas covers `Z`
    have hmem : Sieve.ofArrows _ a ∈ J W :=
      fppf_ofArrows_mem B S hS _ a (fun i ↦ inferInstanceAs (Flat (𝒰.f i)))
        (fun i ↦ inferInstanceAs (LocallyOfFinitePresentation (𝒰.f i)))
        fun x ↦ 𝒰.exists_eq x
    have h₁ : Sheaf.IsLocallySurjective
        (Limits.Sigma.desc fun k : ULift.{u + 1} 𝒰.I₀ ↦ J.uliftYoneda.{u + 1}.map (a k.down)) := by
      refine (Sheaf.isLocallySurjective_sigmaDesc_iff _).2 fun U s ↦ ?_
      refine ⟨_, J.pullback_stable s.down hmem, fun T g hg ↦ ?_⟩
      obtain ⟨_, c, _, ⟨i⟩, h⟩ := hg
      refine ⟨⟨i⟩, ⟨c⟩, ?_⟩
      calc _ = J.uliftYonedaEquiv.{u + 1}
            (J.uliftYoneda.{u + 1}.map c ≫ J.uliftYoneda.{u + 1}.map (a i)) := by
            rw [GrothendieckTopology.uliftYonedaEquiv_comp,
              GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map]
        _ = J.uliftYonedaEquiv.{u + 1}
            (J.uliftYoneda.{u + 1}.map g ≫ J.uliftYoneda.{u + 1}.map s.down) := by
            rw [← Functor.map_comp, ← Functor.map_comp, h]
        _ = _ := by
            rw [← GrothendieckTopology.uliftYonedaEquiv_naturality,
              GrothendieckTopology.uliftYonedaEquiv_uliftYoneda_map]
            rfl
    have h₂ : Sheaf.IsLocallySurjective qS := by
      refine ⟨fun {T} y ↦ ?_⟩
      let ξ : uliftYoneda.{u + 1}.obj T ⟶ Z.obj := uliftYonedaEquiv.symm y
      let p := hqs.rep.snd ξ
      have hcover : Sieve.generate (Presieve.singleton p) ∈ J T := by
        show Sieve.generate (Presieve.singleton p) ∈ B.topology.over (B.obj hS) T
        rw [B.topology.mem_over_iff, Sieve.overEquiv_generate,
          ← Sieve.arrows_generate_map_eq_functorPushforward, Sieve.generate_sieve,
          Presieve.map_singleton]
        exact Space.singleton_mem_bigFppf_topology B p.left
          (hqs.property_snd ξ) (hqe.property ξ (hqs.rep.fst ξ) p (hqs.rep.isPullback ξ))
      refine J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hcover
      rintro _ _ ⟨⟩
      exact ⟨uliftYonedaEquiv (hqs.rep.fst ξ), (uliftYonedaEquiv_comp _ _).symm.trans
        ((congrArg uliftYonedaEquiv (hqs.rep.isPullback ξ).w).trans
          (by simpa only [p, Quiver.Hom.unop_op, ξ, Equiv.apply_symm_apply] using
            (uliftYonedaEquiv_naturality ξ p.op).symm))⟩
    have hfac : (Limits.Sigma.desc fun k : ULift.{u + 1} 𝒰.I₀ ↦
        J.uliftYoneda.{u + 1}.map (a k.down)) ≫ qS =
        Limits.Sigma.desc fun k : ULift.{u + 1} 𝒰.I₀ ↦ J.uliftYoneda.{u + 1}.map (a k.down) ≫ qS :=
      Sigma.hom_ext _ _ fun k ↦ by simp
    rw [← hfac]
    infer_instance

/-- The sheaf represented by an object of the site satisfies the set-theoretic condition of
Stacks 0AIS: it is its own representable surjection, and so is its kernel pair. -/
theorem satisfiesSetTheoreticCondition_uliftYoneda (T : BigFppfOver B S hS) :
    SatisfiesSetTheoreticCondition B S hS
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T) :=
  satisfiesSetTheoreticCondition_uliftYoneda_aux B S hS T

/-- **A representable sheaf is a formal algebraic space.** The sheaf represented by an object of
the big fppf site of `S` is a formal algebraic space over `S`: the affine opens of the object
form a covering as in Definition 0AIM. -/
theorem isFormalAlgebraicSpace_uliftYoneda (T : BigFppfOver B S hS) :
    IsFormalAlgebraicSpace B S hS ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  obtain ⟨K, V, a, ha⟩ := exists_isAffineEtaleCover_of_isAlgebraicSpaceULift B S hS
    ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T)
    (Space.isAlgebraicSpaceULift_uliftYoneda B S hS T)
  exact ⟨satisfiesSetTheoreticCondition_uliftYoneda B S hS T, K, _, a, ha⟩

/-- Coverings as in Definition 0AIM compose: a covering of `G` followed by a covering of each of
its members is a covering of `G`, indexed by the pairs. -/
theorem isAffineEtaleCover_sigma {G : FppfSheaf B S hS} {I : Type (u + 1)}
    {H : I → FppfSheaf B S hS} {ψ' : ∀ i, H i ⟶ G}
    (hψ : ∀ i, IsRepresentableEtale B S hS (ψ' i))
    (hsurj : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc ψ'))
    {K : I → Type (u + 1)} {A : ∀ i, K i → FppfSheaf B S hS} {w : ∀ i k, A i k ⟶ H i}
    (hw : ∀ i, IsAffineEtaleCover B S hS (A i) (w i)) :
    IsAffineEtaleCover B S hS (fun p : (i : I) × K i ↦ A p.1 p.2)
      (fun p ↦ w p.1 p.2 ≫ ψ' p.1) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨fun p ↦ (hw p.1).1 p.2,
    fun p ↦ IsRepresentableEtale.comp B S hS ((hw p.1).2.1 p.2) (hψ p.1), ?_⟩
  have hepiψ : Epi (Sigma.desc ψ') := (Sheaf.isLocallySurjective_iff_epi _).1 hsurj
  have hrepi : Epi (Sigma.desc fun p : (i : I) × K i ↦ w p.1 p.2 ≫ Sigma.ι H p.1) := by
    refine ⟨fun {Z} c d hcd ↦ Sigma.hom_ext _ _ fun i ↦ ?_⟩
    have := (Sheaf.isLocallySurjective_iff_epi _).1 (hw i).2.2
    refine (cancel_epi (Sigma.desc (w i))).1 (Sigma.hom_ext _ _ fun k ↦ ?_)
    simpa using congrArg (fun z ↦ Sigma.ι (fun p : (i : I) × K i ↦ A p.1 p.2) ⟨i, k⟩ ≫ z) hcd
  have hfac : (Sigma.desc fun p : (i : I) × K i ↦ w p.1 p.2 ≫ Sigma.ι H p.1) ≫
      Sigma.desc ψ' = Sigma.desc fun p : (i : I) × K i ↦ w p.1 p.2 ≫ ψ' p.1 :=
    Sigma.hom_ext _ _ fun p ↦ by simp
  refine (Sheaf.isLocallySurjective_iff_epi _).2 ?_
  rw [← hfac]
  exact epi_comp _ _

/-- **Stacks 0AN4, (5) implies (1), in its first step.** Let `f : X ⟶ Y` be a morphism of formal
algebraic spaces over `S`, and let `{Uᵢ ⟶ X}` be a covering as in Definition 0AIM. If every
composite `Uᵢ ⟶ X ⟶ Y` is representable by algebraic spaces, then so is `f`.

At a point `ξ : T ⟶ Y` the fibre product `P = T ×_Y X` is covered by the affine opens of
scheme atlases of the algebraic spaces `T ×_Y Uᵢ`, and satisfies the set-theoretic condition of
Stacks 0AIS by Stacks 0AIP; so it is a formal algebraic space with an atlas by affine schemes,
hence an algebraic space by Stacks 0AIS, observation (2). -/
theorem isRepresentable_of_affineEtaleCover_of_isRepresentable_comp
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    {I : Type (u + 1)} (U : I → FppfSheaf B S hS) (a : ∀ i, U i ⟶ X)
    (ha : IsAffineEtaleCover B S hS U a)
    (h : ∀ i, Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (a i ≫ f).hom) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS f.hom := by
  classical
  intro T ξ
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  let L := sheafToPresheaf J (Type (u + 1))
  let ξS : J.uliftYoneda.{u + 1}.obj T ⟶ Y := ⟨ξ⟩
  let s := pullback.snd ξS f
  have hsq : ∀ {F G H : FppfSheaf B S hS} (p : G ⟶ F) (q : H ⟶ F),
      IsPullback (pullback.fst p q).hom (pullback.snd p q).hom p.hom q.hom :=
    fun p q ↦ (IsPullback.of_hasPullback p q).map L
  -- the base changes `T ×_Y Uᵢ` are algebraic spaces, so are covered by affine schemes
  have hPi : ∀ i, Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback (a i) s).obj := fun i ↦
    Space.isAlgebraicSpaceULift_of_iso B S hS
      ((L.mapIso (pullbackSymmetry (a i) s ≪≫ pullbackLeftPullbackSndIso ξS f (a i)) ≪≫
        (hsq ξS (a i ≫ f)).isoPullback).symm) (h i T ξ)
  choose K V b hb using fun i ↦
    exists_isAffineEtaleCover_of_isAlgebraicSpaceULift B S hS _ (hPi i)
  have hcover := isAffineEtaleCover_sigma B S hS
    (fun i ↦ isRepresentableEtale_pullback_snd B S hS (a i) s (ha.2.1 i))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd s a ha.2.2) hb
  -- the set-theoretic condition, from representable relative products
  have hset : SatisfiesSetTheoreticCondition B S hS (pullback ξS f) :=
    satisfiesSetTheoreticCondition_pullback_of_hasRepresentableRelativeProducts B S hS ξS f
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hY)
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS
        (isFormalAlgebraicSpace_uliftYoneda B S hS T))
      (hasRepresentableRelativeProducts_of_isFormalAlgebraicSpace B S hS hX)
      (satisfiesSetTheoreticCondition_uliftYoneda B S hS T) hX.1
  have hP : Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξS f).obj := by
    refine isAlgebraicSpace_of_affineSchemeAtlas B S hS _
      ⟨hset, _, _, _, hcover.1, hcover.2.1, hcover.2.2⟩
      ⟨_, _, _, hcover.1, fun p ↦ ?_, hcover.2.1, hcover.2.2⟩
    let W := (BigAffineFppf.inclusion B S hS).obj (V p.1 p.2)
    refine ⟨(Over.post B.inclusion).obj W, (V p.1 p.2).property, ⟨?_⟩⟩
    refine ((Sheaf.sheafifiedYonedaIsoUliftYoneda' J).app W).symm ≪≫
      (presheafToSheaf J (Type (u + 1))).mapIso
        (Functor.isoWhiskerRight ?_ uliftFunctor.{u + 1, u})
    let hF := Functor.FullyFaithful.ofFullyFaithful (Over.post (X := B.obj hS) B.inclusion)
    refine NatIso.ofComponents (fun _ ↦ Equiv.toIso hF.homEquiv) fun g ↦ ?_
    ext x
    exact (Over.post B.inclusion).map_comp _ _
  exact Space.isAlgebraicSpaceULift_of_iso B S hS (hsq ξS f).isoPullback hP

end AlgebraicGeometry.FormalSpace

end
