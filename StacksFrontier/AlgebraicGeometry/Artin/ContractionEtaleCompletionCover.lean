module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheafProperty
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationFunctor
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableAfterSourceCover
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.LocallySurjectiveTransfer

/-!
# Completions along a covering family, and étale-local adicness

Let `{p_i : P_i ⟶ P}` be a family of morphisms of presheaves on the big fppf site over `S` whose
images cover `P` locally (for instance the base change of a covering family `{V_i ⟶ V}` of the
site along a morphism `P ⟶ V`), let `T` be a set of points of `P` and let `T_i` be its inverse
image in `P_i`. This file proves that the completions `P_{i,/T_i}` cover the completion `P_{/T}`
of Stacks 0AMC: their completion subfunctors cover the completion subfunctor of `P`, a morphism
out of `P_{/T}` into a sheaf is determined by its restrictions, and the induced morphism from
the coproduct of the `P_{i,/T_i}` to `P_{/T}` is a surjection of sheaves.

As an application, adicness of a morphism `x̂ : V_{/Z} ⟶ W` into a formal algebraic space may be
checked after restricting along the completions `V_{i,/Z_i} ⟶ V_{/Z}` of an étale covering
family `{V_i ⟶ V}` of the site: those restrictions are representable étale (Stacks 0GI0) and
jointly surjective, so representability by algebraic spaces descends along them.

## Main results

* `AlgebraicGeometry.Space.familyImage_sieveOfSection_mem_completionSubfunctor_of_cover`: the
  completion subfunctors of a covering family cover the completion subfunctor.
* `AlgebraicGeometry.Space.hom_ext_completionSheaf_of_cover`: a morphism out of a completion is
  determined by its restrictions to the completions of a covering family.
* `AlgebraicGeometry.Space.isLocallySurjective_sigmaDesc_completionSheafRestrict`: the
  completions of a covering family jointly surject onto the completion.
* `AlgebraicGeometry.Space.familyImage_sieveOfSection_mem_yoneda`: the members of a covering
  family of an object of the site cover its Yoneda presheaf.
* `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_etale_completionSheafRestrict`:
  adicness of a morphism out of `V_{/Z}` into a formal algebraic space is étale local on `V`.

## References

* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
* [Stacks Project, Tag 0AQ2](https://stacks.math.columbia.edu/tag/0AQ2)
* [Stacks Project, Tag 0GI0](https://stacks.math.columbia.edu/tag/0GI0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Completions along a covering family -/

section Cover

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type*}
  {Pi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The completion subfunctors of a covering family cover the completion subfunctor.** If the
images of `p_i : P_i ⟶ P` cover `P` locally and `T_i` is the inverse image of `T ⊆ |P|`, then
every section of the completion subfunctor of `P` along `T` lies locally in the image of one of
the completion subfunctors of the `P_i` along `T_i`. -/
theorem familyImage_sieveOfSection_mem_completionSubfunctor_of_cover (p : ∀ i, Pi i ⟶ P)
    (hcover : ∀ (Z : BigFppfOver B S hS) (x : P.obj (op Z)),
      (familyImage p).sieveOfSection x ∈ BigFppfOver.topology B S hS Z)
    (T : Set (points B S hS P)) (Ti : ∀ i, Set (points B S hS (Pi i)))
    (hTi : ∀ i, Ti i = pointsMap B S hS (Pi i) (p i) ⁻¹' T)
    (Z : BigFppfOver B S hS) (x : (completionSubfunctor B S hS P T).toFunctor.obj (op Z)) :
    (familyImage fun i => completionSubfunctorRestrict B S hS (p i) (Ti i) T
        (hTi i).subset).sieveOfSection x ∈ BigFppfOver.topology B S hS Z := by
  refine (BigFppfOver.topology B S hS).superset_covering ?_ (hcover Z x.1.down)
  rintro Z' g ⟨i, b, hb⟩
  have hbmem : HasImageIn B S hS (Pi i) (Ti i) Z' b := by
    intro q
    have hq := x.2 (⟨q.carrier, q.contained, q.toBase, q.value ≫ g⟩ :
      FieldValuedPoint B S hS (yoneda.obj Z))
    have heq : (p i).app _ ((Pi i).map q.value.op b) =
        P.map (q.value ≫ g).op x.1.down := by
      rw [NatTrans.naturality_apply, hb, op_comp, Functor.map_comp_apply]
    rw [hTi i, Set.mem_preimage]
    exact Set.mem_of_eq_of_mem (congrArg (fun v ↦ (⟨q.carrier, q.contained, q.toBase, v⟩ :
      FieldValuedPoint B S hS P).class B S hS P) heq) hq
  exact ⟨i, ⟨ULift.up b, hbmem⟩, Subtype.ext (congrArg ULift.up hb)⟩

/-- **A morphism out of a completion is determined by its restrictions to the completions of a
covering family.** -/
theorem hom_ext_completionSheaf_of_cover (p : ∀ i, Pi i ⟶ P)
    (hcover : ∀ (Z : BigFppfOver B S hS) (x : P.obj (op Z)),
      (familyImage p).sieveOfSection x ∈ BigFppfOver.topology B S hS Z)
    (T : Set (points B S hS P)) (Ti : ∀ i, Set (points B S hS (Pi i)))
    (hTi : ∀ i, Ti i = pointsMap B S hS (Pi i) (p i) ⁻¹' T)
    {Q : Sheaf (BigFppfOver.topology B S hS) (Type (u + 1))}
    (ψ ψ' : completionSheaf B S hS P T ⟶ Q)
    (hψ : ∀ i, completionSheafRestrict B S hS (p i) (Ti i) T (hTi i).subset ≫ ψ =
      completionSheafRestrict B S hS (p i) (Ti i) T (hTi i).subset ≫ ψ') :
    ψ = ψ' := by
  refine ObjectProperty.hom_ext _
    ((BigFppfOver.topology B S hS).sheafify_hom_ext _ _ Q.property ?_)
  refine hom_ext_of_familyImage_cover _ _
    (fun Z x ↦ familyImage_sieveOfSection_mem_completionSubfunctor_of_cover B S hS p hcover
      T Ti hTi Z x) Q.property _ _ fun i ↦ ?_
  rw [completionSubfunctorRestrict_comp_toSheafify B S hS _ _ _ (hTi i).subset ψ,
    completionSubfunctorRestrict_comp_toSheafify B S hS _ _ _ (hTi i).subset ψ', hψ i]

end Cover

/-- **The completions of a covering family jointly surject onto the completion.** If the images
of `p_i : P_i ⟶ P` cover `P` locally and `T_i` is the inverse image of `T ⊆ |P|`, the morphism
`∐ P_{i,/T_i} ⟶ P_{/T}` is a surjection of sheaves. -/
theorem isLocallySurjective_sigmaDesc_completionSheafRestrict
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {I : Type (u + 1)}
    {Pi : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : ∀ i, Pi i ⟶ P)
    (hcover : ∀ (Z : BigFppfOver B S hS) (x : P.obj (op Z)),
      (familyImage p).sieveOfSection x ∈ BigFppfOver.topology B S hS Z)
    (T : Set (points B S hS P)) (Ti : ∀ i, Set (points B S hS (Pi i)))
    (hTi : ∀ i, Ti i = pointsMap B S hS (Pi i) (p i) ⁻¹' T) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS) :=
      Sheaf.instHasColimitsOfSize
    Sheaf.IsLocallySurjective (Limits.Sigma.desc fun i =>
      completionSheafRestrict B S hS (p i) (Ti i) T (hTi i).subset) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS) :=
    Sheaf.instHasColimitsOfSize
  let J := BigFppfOver.topology B S hS
  let G := (completionSubfunctor B S hS P T).toFunctor
  refine (Sheaf.isLocallySurjective_sigmaDesc_iff _).2 fun U s ↦ ?_
  refine ⟨Sieve.bind (Presheaf.imageSieve (J.toSheafify G) s) fun V g hg ↦
      (familyImage fun i ↦ completionSubfunctorRestrict B S hS (p i) (Ti i) T
        (hTi i).subset).sieveOfSection (Presheaf.localPreimage (J.toSheafify G) s g hg),
    J.bind_covering (Presheaf.imageSieve_mem J (J.toSheafify G) s) fun V g hg ↦
      familyImage_sieveOfSection_mem_completionSubfunctor_of_cover B S hS p hcover T Ti hTi V _,
    ?_⟩
  rintro W k ⟨V, h, g, hg, ⟨i, t, ht⟩, rfl⟩
  refine ⟨i, (J.toSheafify (completionSubfunctor B S hS (Pi i) (Ti i)).toFunctor).app (op W) t,
    ?_⟩
  refine (congrArg (fun φ ↦ φ.app (op W) t) (J.toSheafify_naturality
    (completionSubfunctorRestrict B S hS (p i) (Ti i) T (hTi i).subset)).symm).trans ?_
  rw [NatTrans.comp_app_apply, ht, NatTrans.naturality_apply]
  refine (congrArg (fun x ↦ (J.sheafify G).map h.op x)
    (Presheaf.app_localPreimage (J.toSheafify G) s g hg)).trans ?_
  rw [op_comp, Functor.map_comp_apply]
  rfl

/-- **The members of a covering family cover the Yoneda presheaf.** If `{f_i : V_i ⟶ V}`
generates a covering sieve, the images of the `h_{V_i} ⟶ h_V` cover `h_V` locally. -/
theorem familyImage_sieveOfSection_mem_yoneda {V : BigFppfOver B S hS} {I : Type*}
    (Vi : I → BigFppfOver B S hS) (f : ∀ i, Vi i ⟶ V)
    (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (Z : BigFppfOver B S hS) (x : (yoneda.obj V).obj (op Z)) :
    (familyImage fun i => yoneda.map (f i)).sieveOfSection x ∈
      BigFppfOver.topology B S hS Z :=
  familyImage_cover _ f hf (𝟙 _) (fun i ↦ yoneda.map (f i)) (fun _ ↦ 𝟙 _)
    (fun _ ↦ IsPullback.of_id_snd) Z x

/-- **Adicness is étale local on the base of a completion.** Let `{f_i : V_i ⟶ V}` be a family
of étale morphisms of the site generating a covering sieve, let `Z ⊆ |V|` be closed and let
`x̂ : V_{/Z} ⟶ W` be a morphism into a formal algebraic space. If each restriction of `x̂` to
`V_{i,/Z_i}`, with `Z_i` the inverse image of `Z`, is representable by algebraic spaces, then so
is `x̂`. -/
theorem isRepresentableByAlgebraicSpacesULift_of_etale_completionSheafRestrict
    {V : BigFppfOver B S hS} {I : Type (u + 1)} (Vi : I → BigFppfOver B S hS)
    (f : ∀ i, Vi i ⟶ V) (hf : Sieve.ofArrows Vi f ∈ BigFppfOver.topology B S hS V)
    (het : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (f i)))
    (Z : Set (points B S hS (yoneda.obj V)))
    (hZ : @IsClosed _ (pointTopology B S hS (yoneda.obj V)) Z)
    {W : FormalSpace.FppfSheaf B S hS} (hW : FormalSpace.IsFormalAlgebraicSpace B S hS W)
    (xhat : completionSheaf B S hS (yoneda.obj V) Z ⟶ W)
    (h : ∀ i, IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (completionSheafRestrict B S hS (yoneda.map (f i))
        (pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z) Z
        (fun _ hz => hz) ≫ xhat).hom) :
    IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xhat.hom := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FormalSpace.FppfSheaf B S hS) :=
    Sheaf.instHasColimitsOfSize
  refine FormalSpace.isRepresentableByAlgebraicSpacesULift_of_etaleCover_comp B S hS xhat
    (FormalSpace.satisfiesSetTheoreticCondition_completionSheaf
      (isAlgebraicSpace_yoneda B S hS V) Z hZ) hW
    (fun i ↦ completionSheaf B S hS (yoneda.obj (Vi i))
      (pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z))
    (fun i ↦ completionSheafRestrict B S hS (yoneda.map (f i))
      (pointsMap B S hS (yoneda.obj (Vi i)) (yoneda.map (f i)) ⁻¹' Z) Z (fun _ hz ↦ hz))
    (fun i ↦ ?_) ?_ h
  · exact FormalSpace.isRepresentableEtale_completionSheafMap (isAlgebraicSpace_yoneda B S hS V)
      (isAlgebraicSpace_yoneda B S hS (Vi i)) (yoneda.map (f i))
      ((isEtale_iff_presheaf_of_yoneda B S hS _).2
        ((presheaf_yoneda_map_etale_iff B S hS (f i)).2 (het i)))
  · exact isLocallySurjective_sigmaDesc_completionSheafRestrict B S hS
      (fun i ↦ yoneda.map (f i)) (familyImage_sieveOfSection_mem_yoneda B S hS Vi f hf) Z _
      (fun _ ↦ rfl)

end AlgebraicGeometry.Space

end
