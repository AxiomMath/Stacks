module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.PieceAssembly
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.SquarePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Naturality
public import StacksFrontier.AlgebraicGeometry.Chow.BabyLocalizedChern.CompositeCaps
public import StacksFrontier.AlgebraicGeometry.Chow.GysinAtInfinity.Lift
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.BivariantCommutation

/-!
# Restricting a composite of bivariant classes to pieces

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes locally of finite type over the base of
chapter 42 of the Stacks Project, `a ∈ A^p(X ⟶ Y)` and `b ∈ A^q(Y ⟶ Z)`. Let `X_i ⊆ X`,
`Y_k ⊆ Y`, `Z_j ⊆ Z` be opens with `f(X_i) ⊆ Y_{β(i)}` and `g(Y_k) ⊆ Z_{γ(k)}`. Restriction to
pieces in the sense of Stacks 0FDZ is compatible with the composition of Stacks 0B75:

  `(a ∘ b)|_{X_i ⟶ Z_{γ(β(i))}} = a|_{X_i ⟶ Y_{β(i)}} ∘ b|_{Y_{β(i)} ⟶ Z_{γ(β(i))}}`.

## Main results

* `Stacks.Chow.pieceMap_comp` — the restriction of `f ≫ g` to a piece is the composite of the
  restrictions.
* `Stacks.Chow.bivariantPieceRestriction_bivariantComposite_cap_heq` — the compatibility on cap
  operations.
* `Stacks.Chow.bivariantPieceRestriction_bivariantComposite` — the compatibility as an identity of
  bivariant classes.

## References

* [Stacks Project, Tag 0FDZ](https://stacks.math.columbia.edu/tag/0FDZ)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Geometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {I K J : Type u} (UX : I → X.Opens)
  (UY : K → Y.Opens) (UZ : J → Z.Opens) (β : I → K) (γ : K → J)
  (hβ : ∀ i, UX i ≤ f ⁻¹ᵁ UY (β i)) (hγ : ∀ k, UY k ≤ g ⁻¹ᵁ UZ (γ k))

include hβ hγ in
/-- The pieces of `f` and `g` give pieces of `f ≫ g`. -/
theorem le_preimage_comp (i : I) : UX i ≤ (f ≫ g) ⁻¹ᵁ UZ (γ (β i)) :=
  fun _ hx ↦ hγ (β i) (hβ i hx)

/-- The restriction of `f ≫ g` to a piece is the composite of the restrictions. -/
theorem pieceMap_comp (i : I) :
    pieceMap (f ≫ g) UX UZ (fun i ↦ γ (β i)) (le_preimage_comp f g UX UY UZ β γ hβ hγ) i =
      pieceMap f UX UY β hβ i ≫ pieceMap g UY UZ γ hγ (β i) := by
  refine (cancel_mono (UZ (γ (β i))).ι).1 ?_
  rw [Category.assoc, pieceMap_comp_ι, pieceMap_comp_ι, pieceMap_comp_ι_assoc]

end Geometry

section Cap

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y Z : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (p q : ℤ)
  (a : BivariantClass C G sX sY f hf p) (b : BivariantClass C G sY sZ g hg q)
  {I K J : Type u} (UX : I → X.Opens) (UY : K → Y.Opens) (UZ : J → Z.Opens) (β : I → K)
  (γ : K → J) (hβ : ∀ i, UX i ≤ f ⁻¹ᵁ UY (β i)) (hγ : ∀ k, UY k ≤ g ⁻¹ᵁ UZ (γ k)) (i : I)
  (hgysO : G.IsNaturalUnderOpenImmersion) (hgys : G.IsNaturalUnderBaseChangeIso)
  (hgysc : G.IsNaturalUnderPullbackCompPushforward)

/-- **Stacks 0FDZ and 0B75: restriction to pieces commutes with composition**, on cap
operations: for a test scheme `t : T ⟶ Z_{γ(β(i))}`,

  `(a ∘ b)|_i ∩ α = a|_i ∩ (b|_{β(i)} ∩ α)`,

the two sides lying on the base changes of `X_i ⟶ Z_{γ(β(i))}` along `t`, written once as the
restriction of `f ≫ g` and once as the composite of the restrictions. -/
theorem bivariantPieceRestriction_bivariantComposite_cap_heq {T : Scheme.{u}}
    (t : T ⟶ (UZ (γ (β i)) : Scheme.{u})) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ ((UZ (γ (β i))).ι ≫ sZ)) k) :
    (bivariantPieceRestriction C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q)
        UX UZ (fun i ↦ γ (β i)) (le_preimage_comp f g UX UY UZ β γ hβ hγ) i hgysO
        (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc)).cap t k α ≍
      bivariantCompositeCap C G ((UX i).ι ≫ sX) ((UY (β i)).ι ≫ sY) ((UZ (γ (β i))).ι ≫ sZ)
        (pieceMap f UX UY β hβ i) (pieceMap g UY UZ γ hγ (β i))
        (pieceMap_comp_structureMorphism C sX sY f hf UX UY β hβ i)
        (pieceMap_comp_structureMorphism C sY sZ g hg UY UZ γ hγ (β i))
        (properPushforwardDescends C) p q
        (bivariantPieceRestriction C G sX sY f hf p UX UY β hβ i hgysO a)
        (bivariantPieceRestriction C G sY sZ g hg q UY UZ γ hγ (β i) hgysO b) t k α := by
  set α' := chowGroupCongr C (Category.assoc t (UZ (γ (β i))).ι sZ).symm k α
  set B := b.cap (t ≫ (UZ (γ (β i))).ι) k α'
  -- the open immersion `Y_k ×_{Z_j} T ⟶ Y ×_Z T` and its base change along `f`
  set v := pieceComparison g UY UZ γ hγ (β i) t
  have hm : v ≫ pullback.fst g (t ≫ (UZ (γ (β i))).ι) =
      (pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι :=
    opensPullbackComparison_fst _ _ _ _ _ _
  set v' := baseChangeMapOfEq f (pullback.fst g (t ≫ (UZ (γ (β i))).ι)) v
    ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) hm
  have : IsOpenImmersion v' :=
    MorphismProperty.of_isPullback (isPullback_baseChangeMapOfEq f _ v _ hm) inferInstance
  have hvY : v ≫ (pullback.fst g (t ≫ (UZ (γ (β i))).ι) ≫ sY) =
      ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) ≫ sY := by
    rw [← Category.assoc, hm]
  have hbase : v' ≫ (pullback.fst f (pullback.fst g (t ≫ (UZ (γ (β i))).ι)) ≫ sX) =
      pullback.fst f ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) ≫ sX :=
    baseChangeMapOfEq_comp_structure sX f _ v _ hm
  set Y0 := a.cap (pullback.fst g (t ≫ (UZ (γ (β i))).ι)) (k - q) B
  -- capping with `a` commutes with the restriction to `Y_k ×_{Z_j} T`
  have hcap := BivariantClass.cap_chowGroupRestrict C G sX sY f hf p a
    (pullback.fst g (t ≫ (UZ (γ (β i))).ι)) v
    ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) hm v'
    (isPullback_baseChangeMapOfEq f _ v _ hm)
    (baseChangeMapOfEq_fst _ _ _ _ _) (k - q) hvY hbase B
  -- the open immersion `X_i ×_{Y_k} (Y_k ×_{Z_j} T) ⟶ X ×_Y (Y_k ×_{Z_j} T)`
  set w := pieceComparison f UX UY β hβ i (pullback.fst (pieceMap g UY UZ γ hγ (β i)) t)
  have hw : w ≫ (pullback.fst f
        ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) ≫ sX) =
      pullback.fst (pieceMap f UX UY β hβ i) (pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫
        ((UX i).ι ≫ sX) :=
    pieceComparison_comp_structureMorphism f UX UY β hβ i
      (pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) sX
  -- the right-hand side
  have hR : bivariantCompositeCap C G ((UX i).ι ≫ sX) ((UY (β i)).ι ≫ sY)
      ((UZ (γ (β i))).ι ≫ sZ) (pieceMap f UX UY β hβ i) (pieceMap g UY UZ γ hγ (β i))
      (pieceMap_comp_structureMorphism C sX sY f hf UX UY β hβ i)
      (pieceMap_comp_structureMorphism C sY sZ g hg UY UZ γ hγ (β i))
      (properPushforwardDescends C) p q
      (bivariantPieceRestriction C G sX sY f hf p UX UY β hβ i hgysO a)
      (bivariantPieceRestriction C G sY sZ g hg q UY UZ γ hγ (β i) hgysO b) t k α =
      properChowPushforward C
        (pullback.fst (pieceMap f UX UY β hβ i) (pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫
          ((UX i).ι ≫ sX))
        (pullback.fst ((pieceMap f UX UY β hβ i) ≫ (pieceMap g UY UZ γ hγ (β i))) t ≫
          ((UX i).ι ≫ sX))
        (pullbackRightPullbackFstIso (pieceMap g UY UZ γ hγ (β i)) t (pieceMap f UX UY β hβ i)).hom
        (pullbackRightPullbackFstIso_hom_comp_fst_comp _ (pieceMap f UX UY β hβ i)
          (pieceMap g UY UZ γ hγ (β i)) t) (k - q - p)
        (properPushforwardDescends C _ _ _ _ _)
        (chowGroupRestrict C
          (pullback.fst f ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) ≫ sX)
          (pullback.fst (pieceMap f UX UY β hβ i) (pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫
            ((UX i).ι ≫ sX)) w hw (k - q - p)
          (chowGroupRestrict C (pullback.fst f (pullback.fst g (t ≫ (UZ (γ (β i))).ι)) ≫ sX)
            (pullback.fst f ((pullback.fst (pieceMap g UY UZ γ hγ (β i)) t) ≫ (UY (β i)).ι) ≫ sX)
            v' hbase (k - q - p) Y0)) := by
    rw [bivariantCompositeCap_apply, hcap]
    congr 1
  refine HEq.trans ?_ (heq_of_eq hR.symm)
  rw [chowGroupRestrict_comp]
  -- the left-hand side
  have hcomp := pieceMap_comp f g UX UY UZ β γ hβ hγ i
  set pcfg := pieceComparison (f ≫ g) UX UZ (fun i ↦ γ (β i))
    (le_preimage_comp f g UX UY UZ β γ hβ hγ) i t
  set A := (pullbackRightPullbackFstIso g (t ≫ (UZ (γ (β i))).ι) f).hom
  set Ai := (pullbackRightPullbackFstIso (pieceMap g UY UZ γ hγ (β i)) t
    (pieceMap f UX UY β hβ i)).hom
  set A'' := Ai ≫ (pullback.congrHom hcomp.symm (rfl : t = t)).hom
  have hsq : IsPullback (w ≫ v') A'' A pcfg := by
    refine IsPullback.of_vert_isIso ⟨pullback.hom_ext ?_ ?_⟩
    · simp [A, A'', Ai, pcfg, w, v', pieceComparison]
    · simp [A, A'', Ai, pcfg, w, v', pieceComparison, v, opensPullbackComparison_snd_assoc]
  rw [bivariantPieceRestriction_cap, bivariantPieceRestrictionCap_apply, bivariantComposite_cap]
  refine (GysinAtInfinity.chowGroupRestrict_chowGroupDegreeEquiv_heq C _ _ _ _ _ _).trans ?_
  have hpush := chowGroupRestrict_properChowPushforward C _ _ _ _ A
    (pullbackRightPullbackFstIso_hom_comp_fst_comp sX f g (t ≫ (UZ (γ (β i))).ι))
    (w ≫ v') (by rw [Category.assoc, hbase, hw]) pcfg
    (pieceComparison_comp_structureMorphism (f ≫ g) UX UZ (fun i ↦ γ (β i))
      (le_preimage_comp f g UX UY UZ β γ hβ hγ) i t sX) A''
    (by rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst_assoc, Category.comp_id,
      ← Category.assoc, pullbackRightPullbackFstIso_hom_fst])
    hsq (k - q - p) (properPushforwardDescends C _ _ _ _ _)
    (properPushforwardDescends C _ _ _ _ _) Y0
  refine (heq_of_eq hpush).trans ?_
  exact chowPush_heq_of_pullback_comp C ((UX i).ι ≫ sX) _ hcomp t A'' Ai
    (by simp [A'']) (by simp [A'']) _ _ (k - q - p) _

/-- **Stacks 0FDZ and 0B75: restriction to pieces commutes with composition**, as an identity of
bivariant classes, the composite of the restrictions being read at the restriction of `f ≫ g`
through `Stacks.Chow.pieceMap_comp`. -/
theorem bivariantPieceRestriction_bivariantComposite :
    bivariantPieceRestriction C G sX sZ (f ≫ g) (comp_comp_structureMorphism_eq hf hg) (p + q)
        UX UZ (fun i ↦ γ (β i)) (le_preimage_comp f g UX UY UZ β γ hβ hγ) i hgysO
        (bivariantComposite C G sX sY sZ f g hf hg p q a b hgys hgysc) =
      bivariantClassCongr C G ((UX i).ι ≫ sX) ((UZ (γ (β i))).ι ≫ sZ)
        (pieceMap_comp f g UX UY UZ β γ hβ hγ i).symm _ _ (p + q)
        (bivariantComposite C G ((UX i).ι ≫ sX) ((UY (β i)).ι ≫ sY) ((UZ (γ (β i))).ι ≫ sZ)
          (pieceMap f UX UY β hβ i) (pieceMap g UY UZ γ hγ (β i))
          (pieceMap_comp_structureMorphism C sX sY f hf UX UY β hβ i)
          (pieceMap_comp_structureMorphism C sY sZ g hg UY UZ γ hγ (β i)) p q
          (bivariantPieceRestriction C G sX sY f hf p UX UY β hβ i hgysO a)
          (bivariantPieceRestriction C G sY sZ g hg q UY UZ γ hγ (β i) hgysO b) hgys hgysc) := by
  refine BivariantClass.ext C G _ _ _ _ _ fun {T} t _ k α ↦ eq_of_heq ?_
  refine (bivariantPieceRestriction_bivariantComposite_cap_heq C G sX sY sZ f g hf hg p q a b UX
    UY UZ β γ hβ hγ i hgysO hgys hgysc t k α).trans ?_
  refine HEq.trans ?_ (bivariantClassCongr_cap_heq C G _ _ _ _ _ _ _ t k α).symm
  rw [bivariantComposite_cap]
  exact (chowGroupDegreeEquiv_heq C _ _ _).symm

end Cap

end Stacks.Chow

end
