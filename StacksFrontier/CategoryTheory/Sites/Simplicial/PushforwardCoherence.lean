module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousCompCoherence

/-!
# Coherence of the direct-image comparisons of a simplicial-site situation

For a simplicial-site situation `S` (Stacks 09WE) the direct images of the induced morphisms of
topoi come with two canonical comparisons, `SimplicialSiteSituation.pushforwardId` and
`SimplicialSiteSituation.pushforwardCompSymm`. This file proves that those comparisons are
coherent: they satisfy the two unit laws and the cocycle law, so that `φ ↦ (f_φ)_*` is a
pseudofunctor on the (locally discrete) simplex category.

This is the input that Stacks 09WF leaves implicit. Through
`CategoryTheory.Adjunction.leftAdjointCompIso_comp_id`, `_id_comp` and `_assoc` of Mathlib,
together with the identifications of
`StacksFrontier.CategoryTheory.Sites.Simplicial.SheavesPseudofunctorBridge`, the three laws below
transfer to the inverse-image comparisons `canonicalIdentityComparison` and
`canonicalCompositionComparison`, which is what the diagram of component sheaf categories needs.

## Main results

* `CategoryTheory.Functor.sheafPushforwardContinuousComp'_comp_id`,
  `_id_comp`, `_assoc`: the two unit laws and the cocycle law for the comparisons of direct
  images along *continuous* site functors. These are the case (A) ingredients, and they are
  statements about Mathlib's `Functor.sheafPushforwardContinuousComp'` alone.
* `CategoryTheory.sheafPushforwardCocontinuousCompIso_comp_id`, `_id_comp`, `_assoc`: the same
  three laws for the comparisons of direct images along *cocontinuous* site functors. These are
  the case (B) ingredients; they are proved by transporting the presheaf-level laws
  `ranOpCompIso_id_left`, `ranOpCompIso_id_right` and `ranOpCompIso_assoc` through the fully
  faithful functor `sheafToPresheaf`.
* `CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm_comp_id`, `_id_comp`, `_assoc`:
  the three laws for a simplicial-site situation. Each one covers both cases of the situation in
  a single statement, because `pushforwardId` and `pushforwardCompSymm` are single declarations
  defined by a match on the case.

## Implementation notes

`pushforwardId` and `pushforwardCompSymm` are not two declarations, one per case: they are each
one declaration defined by `rcases` on the case of the situation. So there is no statement of
"the unit law in case (A)" about a `SimplicialSiteSituation`, and the three laws below each
discharge both branches. What *can* be isolated per case, and is isolated here, are the general
coherence statements about Mathlib's continuous and cocontinuous pushforward comparisons.

The unit and cocycle laws are stated with a transport `pushforwardCongr` along an equality of
simplex maps, matching the `eqToHom` that appears in the coherence axioms of a pseudofunctor
out of a locally discrete bicategory. The general per-case lemmas take the underlying equalities
of site functors as hypotheses and the induced equality of pushforward functors as a further
hypothesis; since `Eq` is a subsingleton, any proof of the latter may be supplied, so the lemmas
apply directly to whatever transport the caller has.

## References

* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Functor CategoryTheory.SimplicialSiteSituation

universe w v₁ v₂ u₁ u₂ u

namespace CategoryTheory

/-! ### Case (A): comparisons of direct images along continuous site functors -/

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (A : Type w) [Category A] (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/-- The right unit law for the comparison of direct images along continuous site functors:
composing with a site functor isomorphic to the identity on the target is, on direct images,
the identity comparison of that site functor. -/
theorem sheafPushforwardContinuousComp'_comp_id {F FG : C ⥤ D} {I : D ⥤ D}
    [F.IsContinuous J K] [FG.IsContinuous J K] [I.IsContinuous K K]
    (hFI : F ⋙ I = FG) (hI : I = 𝟭 D)
    (hpf : FG.sheafPushforwardContinuous A J K = F.sheafPushforwardContinuous A J K) :
    sheafPushforwardContinuousComp' (eqToIso hFI) A J K K ≪≫ eqToIso hpf =
      isoWhiskerRight (sheafPushforwardContinuousId' (eqToIso hI) A K)
        (F.sheafPushforwardContinuous A J K) ≪≫ leftUnitor _ := by
  subst hFI
  subst hI
  have h : hpf = rfl := rfl
  subst h
  ext X : 3
  apply Sheaf.hom_ext
  ext x
  simp [sheafPushforwardContinuousComp', sheafPushforwardContinuousId',
    sheafPushforwardContinuousIso, sheafPushforwardContinuousNatTrans,
    sheafPushforwardContinuousComp, sheafPushforwardContinuousId]
  rfl

/-- The left unit law for the comparison of direct images along continuous site functors:
composing with a site functor isomorphic to the identity on the source is, on direct images,
the identity comparison of that site functor. -/
theorem sheafPushforwardContinuousComp'_id_comp {F FG : C ⥤ D} {I : C ⥤ C}
    [F.IsContinuous J K] [FG.IsContinuous J K] [I.IsContinuous J J]
    (hIF : I ⋙ F = FG) (hI : I = 𝟭 C)
    (hpf : FG.sheafPushforwardContinuous A J K = F.sheafPushforwardContinuous A J K) :
    sheafPushforwardContinuousComp' (eqToIso hIF) A J J K ≪≫ eqToIso hpf =
      isoWhiskerLeft (F.sheafPushforwardContinuous A J K)
        (sheafPushforwardContinuousId' (eqToIso hI) A J) ≪≫ rightUnitor _ := by
  subst hIF
  subst hI
  have h : hpf = rfl := rfl
  subst h
  ext X : 3
  apply Sheaf.hom_ext
  ext x
  simp [sheafPushforwardContinuousComp', sheafPushforwardContinuousId',
    sheafPushforwardContinuousIso, sheafPushforwardContinuousNatTrans,
    sheafPushforwardContinuousComp, sheafPushforwardContinuousId]
  rfl

end Functor

/-- The cocycle law for the comparison of direct images along continuous site functors: the two
ways of comparing the direct image along a triple composition with the composition of the three
direct images agree. -/
theorem Functor.sheafPushforwardContinuousComp'_assoc
    {C₀ : Type*} [Category* C₀] {C₁ : Type*} [Category* C₁] {C₂ : Type*} [Category* C₂]
    {C₃ : Type*} [Category* C₃] (A : Type w) [Category A]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
    {a : C₀ ⥤ C₁} {b : C₁ ⥤ C₂} {c : C₂ ⥤ C₃}
    {AB : C₀ ⥤ C₂} {BC : C₁ ⥤ C₃} {T T' : C₀ ⥤ C₃}
    [a.IsContinuous J₀ J₁] [b.IsContinuous J₁ J₂] [c.IsContinuous J₂ J₃]
    [AB.IsContinuous J₀ J₂] [BC.IsContinuous J₁ J₃]
    [T.IsContinuous J₀ J₃] [T'.IsContinuous J₀ J₃]
    (hab : a ⋙ b = AB) (hbc : b ⋙ c = BC) (hT : AB ⋙ c = T) (hT' : a ⋙ BC = T')
    (hpf : T.sheafPushforwardContinuous A J₀ J₃ = T'.sheafPushforwardContinuous A J₀ J₃) :
    isoWhiskerLeft (c.sheafPushforwardContinuous A J₂ J₃)
          (sheafPushforwardContinuousComp' (eqToIso hab) A J₀ J₁ J₂) ≪≫
        sheafPushforwardContinuousComp' (eqToIso hT) A J₀ J₂ J₃ ≪≫ eqToIso hpf =
      (associator _ _ _).symm ≪≫
        isoWhiskerRight (sheafPushforwardContinuousComp' (eqToIso hbc) A J₁ J₂ J₃)
            (a.sheafPushforwardContinuous A J₀ J₁) ≪≫
          sheafPushforwardContinuousComp' (eqToIso hT') A J₀ J₁ J₃ := by
  subst hab
  subst hbc
  subst hT
  subst hT'
  have h : hpf = rfl := rfl
  subst h
  ext X : 3
  apply Sheaf.hom_ext
  ext x
  simp [sheafPushforwardContinuousComp', sheafPushforwardContinuousIso,
    sheafPushforwardContinuousNatTrans, sheafPushforwardContinuousComp]
  rfl

/-! ### Bridges between the sheaf-level and presheaf-level cocontinuous comparisons -/

/-- The comparison of two right adjoints of the identity functor, the second being the identity
adjunction, is the counit of the first. -/
theorem Adjunction.rightAdjointUniq_id_hom_app {A : Type*} [Category* A] {R : A ⥤ A}
    (adj : 𝟭 A ⊣ R) (X : A) :
    (Adjunction.rightAdjointUniq adj Adjunction.id).hom.app X = adj.counit.app X := by
  have h := Adjunction.homEquiv_symm_rightAdjointUniq_hom_app adj (Adjunction.id (C := A)) X
  rw [Adjunction.homEquiv_counit] at h
  simpa using h

section Cocontinuous

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D] {E : Type u}
  [SmallCategory E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : GrothendieckTopology E)

/-- On underlying presheaves, the sheaf-level compositor of direct images along cocontinuous
site functors is the presheaf-level compositor of right Kan extensions. -/
theorem sheafPushforwardCocontinuousCompIso_hom_app_hom (u : C ⥤ D) (v : D ⥤ E)
    [u.IsCocontinuous J K] [v.IsCocontinuous K L] (X : Sheaf J (Type u)) :
    ((sheafPushforwardCocontinuousCompIso J K L u v).hom.app X).hom =
      (ranOpCompIso u v).hom.app X.obj := by
  dsimp only [sheafPushforwardCocontinuousCompIso]
  exact (sheafToPresheaf L (Type u)).map_preimage _

/-- The inverse form of `sheafPushforwardCocontinuousCompIso_hom_app_hom`. -/
theorem sheafPushforwardCocontinuousCompIso_inv_app_hom (u : C ⥤ D) (v : D ⥤ E)
    [u.IsCocontinuous J K] [v.IsCocontinuous K L] (X : Sheaf J (Type u)) :
    ((sheafPushforwardCocontinuousCompIso J K L u v).inv.app X).hom =
      (ranOpCompIso u v).inv.app X.obj := by
  dsimp only [sheafPushforwardCocontinuousCompIso]
  exact (sheafToPresheaf L (Type u)).map_preimage _

/-- The direct image along a cocontinuous site functor acts on underlying presheaves by the
right Kan extension. -/
theorem Functor.sheafPushforwardCocontinuous_map_hom (v : D ⥤ E) [v.IsCocontinuous K L]
    {X Y : Sheaf K (Type u)} (g : X ⟶ Y) :
    ((v.sheafPushforwardCocontinuous (Type u) K L).map g).hom = v.op.ran.map g.hom := rfl

/-- On underlying presheaves, the sheaf-level identification of the direct image along the
identity site functor with the identity functor is the presheaf-level one. -/
theorem rightAdjointUniq_sheafAdjunctionCocontinuous_id_hom_app_hom (X : Sheaf J (Type u)) :
    ((Adjunction.rightAdjointUniq
        (((𝟭 C).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
          (Functor.sheafPushforwardContinuousId (Type u) J)) Adjunction.id).hom.app X).hom =
      (Adjunction.rightAdjointUniq ((𝟭 C).op.ranAdjunction (Type u))
        Adjunction.id).hom.app X.obj := by
  rw [Adjunction.rightAdjointUniq_id_hom_app, Adjunction.rightAdjointUniq_id_hom_app,
    Adjunction.ofNatIsoLeft_counit]
  simp only [NatTrans.comp_app, Iso.refl_inv, Functor.sheafPushforwardContinuousId,
    ObjectProperty.FullSubcategory.comp_hom]
  exact Functor.sheafAdjunctionCocontinuous_counit_app_hom (𝟭 C) (Type u) J J X

/-- The transport of a direct image along a cocontinuous site functor along a reflexivity
proof is the identity. -/
theorem SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl {F : C ⥤ D}
    [F.IsCocontinuous J K] :
    cocontinuousPushforwardIsoOfEq.{u, u, u, u, u} J K (rfl : F = F) = Iso.refl _ := rfl

/-! ### Case (B): comparisons of direct images along cocontinuous site functors -/

/-- The right unit law for the comparison of direct images along cocontinuous site functors. -/
theorem sheafPushforwardCocontinuousCompIso_comp_id {I : C ⥤ C} {v IV : C ⥤ D}
    [I.IsCocontinuous J J] [v.IsCocontinuous J K] [IV.IsCocontinuous J K]
    [(I ⋙ v).IsCocontinuous J K]
    (hI : I = 𝟭 C) (hIv : I ⋙ v = IV)
    (hpf : IV.sheafPushforwardCocontinuous (Type u) J K
      = v.sheafPushforwardCocontinuous (Type u) J K) :
    ((sheafPushforwardCocontinuousCompIso J J K I v).symm ≪≫
        cocontinuousPushforwardIsoOfEq J K hIv) ≪≫ eqToIso hpf =
      Functor.isoWhiskerRight
          (cocontinuousPushforwardIsoOfEq J J hI ≪≫
            Adjunction.rightAdjointUniq
              (((𝟭 C).sheafAdjunctionCocontinuous (Type u) J J).ofNatIsoLeft
                (Functor.sheafPushforwardContinuousId (Type u) J)) Adjunction.id)
          (v.sheafPushforwardCocontinuous (Type u) J K) ≪≫ Functor.leftUnitor _ := by
  subst hI
  subst hIv
  have h2 : hpf = rfl := rfl
  subst h2
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl,
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Sheaf.hom_ext
  have h := NatTrans.congr_app (ranOpCompIso_id_left v) X.obj
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app] at h
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, eqToIso_refl, Functor.id_obj,
    Category.id_comp, Category.comp_id, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  exact (Category.comp_id _).trans
    ((sheafPushforwardCocontinuousCompIso_inv_app_hom J J K (𝟭 C) v X).trans
      ((((ranOpCompIso _ _).app _).inv_ext' h).symm.trans
        ((congrArg v.op.ran.map
          (rightAdjointUniq_sheafAdjunctionCocontinuous_id_hom_app_hom J X).symm).trans
            (Category.comp_id _).symm)))

/-- The left unit law for the comparison of direct images along cocontinuous site functors. -/
theorem sheafPushforwardCocontinuousCompIso_id_comp {u UI : C ⥤ D} {I : D ⥤ D}
    [u.IsCocontinuous J K] [I.IsCocontinuous K K] [UI.IsCocontinuous J K]
    [(u ⋙ I).IsCocontinuous J K]
    (hI : I = 𝟭 D) (huI : u ⋙ I = UI)
    (hpf : UI.sheafPushforwardCocontinuous (Type u) J K
      = u.sheafPushforwardCocontinuous (Type u) J K) :
    ((sheafPushforwardCocontinuousCompIso J K K u I).symm ≪≫
        cocontinuousPushforwardIsoOfEq J K huI) ≪≫ eqToIso hpf =
      Functor.isoWhiskerLeft (u.sheafPushforwardCocontinuous (Type u) J K)
          (cocontinuousPushforwardIsoOfEq K K hI ≪≫
            Adjunction.rightAdjointUniq
              (((𝟭 D).sheafAdjunctionCocontinuous (Type u) K K).ofNatIsoLeft
                (Functor.sheafPushforwardContinuousId (Type u) K)) Adjunction.id) ≪≫
        Functor.rightUnitor _ := by
  subst hI
  subst huI
  have h2 : hpf = rfl := rfl
  subst h2
  rw [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl,
    SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply Sheaf.hom_ext
  have h := NatTrans.congr_app (ranOpCompIso_id_right u) X.obj
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app] at h
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, eqToIso_refl,
    Category.id_comp, Category.comp_id, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.FullSubcategory.id_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact (Category.comp_id _).trans
    ((sheafPushforwardCocontinuousCompIso_inv_app_hom J K K u (𝟭 D) X).trans
      ((((ranOpCompIso _ _).app _).inv_ext' h).symm.trans
        ((rightAdjointUniq_sheafAdjunctionCocontinuous_id_hom_app_hom K
          ((u.sheafPushforwardCocontinuous (Type u) J K).obj X)).symm.trans
            (Category.comp_id _).symm)))

end Cocontinuous

/-- The cocycle law for the comparison of direct images along cocontinuous site functors: the
two ways of comparing the direct image along a triple composition with the composition of the
three direct images agree. -/
theorem sheafPushforwardCocontinuousCompIso_assoc
    {C₀ : Type u} [SmallCategory C₀] {C₁ : Type u} [SmallCategory C₁]
    {C₂ : Type u} [SmallCategory C₂] {C₃ : Type u} [SmallCategory C₃]
    (J₀ : GrothendieckTopology C₀) (J₁ : GrothendieckTopology C₁)
    (J₂ : GrothendieckTopology C₂) (J₃ : GrothendieckTopology C₃)
    {a : C₃ ⥤ C₂} {b : C₂ ⥤ C₁} {c : C₁ ⥤ C₀}
    {BC : C₂ ⥤ C₀} {AB : C₃ ⥤ C₁} {T T' : C₃ ⥤ C₀}
    [a.IsCocontinuous J₃ J₂] [b.IsCocontinuous J₂ J₁] [c.IsCocontinuous J₁ J₀]
    [BC.IsCocontinuous J₂ J₀] [AB.IsCocontinuous J₃ J₁]
    [T.IsCocontinuous J₃ J₀] [T'.IsCocontinuous J₃ J₀]
    [(b ⋙ c).IsCocontinuous J₂ J₀] [(a ⋙ b).IsCocontinuous J₃ J₁]
    [(a ⋙ BC).IsCocontinuous J₃ J₀] [(AB ⋙ c).IsCocontinuous J₃ J₀]
    (hbc : b ⋙ c = BC) (hab : a ⋙ b = AB) (hT : a ⋙ BC = T) (hT' : AB ⋙ c = T')
    (hpf : T.sheafPushforwardCocontinuous (Type u) J₃ J₀
      = T'.sheafPushforwardCocontinuous (Type u) J₃ J₀) :
    Functor.isoWhiskerLeft (a.sheafPushforwardCocontinuous (Type u) J₃ J₂)
          ((sheafPushforwardCocontinuousCompIso J₂ J₁ J₀ b c).symm ≪≫
            cocontinuousPushforwardIsoOfEq J₂ J₀ hbc) ≪≫
        (((sheafPushforwardCocontinuousCompIso J₃ J₂ J₀ a BC).symm ≪≫
          cocontinuousPushforwardIsoOfEq J₃ J₀ hT) ≪≫ eqToIso hpf) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
            ((sheafPushforwardCocontinuousCompIso J₃ J₂ J₁ a b).symm ≪≫
              cocontinuousPushforwardIsoOfEq J₃ J₁ hab)
            (c.sheafPushforwardCocontinuous (Type u) J₁ J₀) ≪≫
          ((sheafPushforwardCocontinuousCompIso J₃ J₁ J₀ AB c).symm ≪≫
            cocontinuousPushforwardIsoOfEq J₃ J₀ hT') := by
  subst hbc
  subst hab
  subst hT
  subst hT'
  have h2 : hpf = rfl := rfl
  subst h2
  simp only [SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq_refl]
  refine Iso.ext ((Iso.inv_eq_inv _ _).mp ?_)
  apply NatTrans.ext
  funext X
  apply Sheaf.hom_ext
  have h := NatTrans.congr_app (ranOpCompIso_assoc a b c) X.obj
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at h
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.refl_inv, eqToIso_refl,
    Category.id_comp, Category.comp_id, Category.assoc, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    sheafPushforwardCocontinuousCompIso_hom_app_hom,
    Functor.sheafPushforwardCocontinuous_map_hom]
  exact (Category.id_comp _).trans h

/-! ### The three coherence laws of a simplicial-site situation -/

namespace SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u})

/-- The transport of a direct image along an equality of simplex maps. This is the `eqToHom`
that appears on the right of the coherence axioms of a pseudofunctor out of a locally discrete
bicategory. -/
noncomputable def pushforwardCongr {m n : SimplexCategory} {φ₁ φ₂ : m ⟶ n} (h : φ₁ = φ₂) :
    (S.transitionMorphism φ₁).pushforward ≅ (S.transitionMorphism φ₂).pushforward :=
  eqToIso (by subst h; rfl)

/-- The right unit law for the direct-image comparisons of a simplicial-site situation: the
compositor at `ψ ≫ 𝟙` is the unit comparison in the first variable. -/
theorem pushforwardCompSymm_comp_id {l m : SimplexCategory} (ψ : l ⟶ m) :
    S.pushforwardCompSymm ψ (𝟙 m) ≪≫ S.pushforwardCongr (Category.comp_id ψ) =
      Functor.isoWhiskerRight (S.pushforwardId m) (S.transitionMorphism ψ).pushforward ≪≫
        Functor.leftUnitor _ := by
  rcases S with ⟨C | C⟩
  · have := (C.isMorphismOfSites ψ).isContinuous
    have := (C.isMorphismOfSites (𝟙 m)).isContinuous
    have := (C.isMorphismOfSites (ψ ≫ 𝟙 m)).isContinuous
    dsimp only [pushforwardCompSymm, pushforwardId, pushforwardCongr, id]
    exact Functor.sheafPushforwardContinuousComp'_comp_id (Type u) _ _ _ _ _
  · have := C.isCocontinuous (𝟙 m).op
    have := C.isCocontinuous ψ.op
    have := C.isCocontinuous (ψ ≫ 𝟙 m).op
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map (𝟙 m).op).toFunctor
      (C.underlying.map ψ.op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op m)))
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op l))))
    dsimp only [pushforwardCompSymm, pushforwardId, pushforwardCongr, id, transitionMorphism,
      gStar]
    exact sheafPushforwardCocontinuousCompIso_comp_id _ _ _ _ _

/-- The left unit law for the direct-image comparisons of a simplicial-site situation: the
compositor at `𝟙 ≫ φ` is the unit comparison in the second variable. -/
theorem pushforwardCompSymm_id_comp {m n : SimplexCategory} (φ : m ⟶ n) :
    S.pushforwardCompSymm (𝟙 m) φ ≪≫ S.pushforwardCongr (Category.id_comp φ) =
      Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward (S.pushforwardId m) ≪≫
        Functor.rightUnitor _ := by
  rcases S with ⟨C | C⟩
  · have := (C.isMorphismOfSites φ).isContinuous
    have := (C.isMorphismOfSites (𝟙 m)).isContinuous
    have := (C.isMorphismOfSites (𝟙 m ≫ φ)).isContinuous
    dsimp only [pushforwardCompSymm, pushforwardId, pushforwardCongr, id]
    exact Functor.sheafPushforwardContinuousComp'_id_comp (Type u) _ _ _ _ _
  · have := C.isCocontinuous (𝟙 m).op
    have := C.isCocontinuous φ.op
    have := C.isCocontinuous (𝟙 m ≫ φ).op
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map φ.op).toFunctor
      (C.underlying.map (𝟙 m).op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op m))))
    dsimp only [pushforwardCompSymm, pushforwardId, pushforwardCongr, id, transitionMorphism,
      gStar]
    exact sheafPushforwardCocontinuousCompIso_id_comp _ _ _ _ _

/-- The cocycle law for the direct-image comparisons of a simplicial-site situation: the two
ways of comparing the direct image along a triple composite of simplex maps with the
composition of the three direct images agree. -/
theorem pushforwardCompSymm_assoc {k l m n : SimplexCategory}
    (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward (S.pushforwardCompSymm χ ψ) ≪≫
        S.pushforwardCompSymm (χ ≫ ψ) φ ≪≫ S.pushforwardCongr (Category.assoc χ ψ φ) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (S.pushforwardCompSymm ψ φ)
            (S.transitionMorphism χ).pushforward ≪≫
          S.pushforwardCompSymm χ (ψ ≫ φ) := by
  rcases S with ⟨C | C⟩
  · have := (C.isMorphismOfSites χ).isContinuous
    have := (C.isMorphismOfSites ψ).isContinuous
    have := (C.isMorphismOfSites φ).isContinuous
    have := (C.isMorphismOfSites (χ ≫ ψ)).isContinuous
    have := (C.isMorphismOfSites (ψ ≫ φ)).isContinuous
    have := (C.isMorphismOfSites ((χ ≫ ψ) ≫ φ)).isContinuous
    have := (C.isMorphismOfSites (χ ≫ ψ ≫ φ)).isContinuous
    dsimp only [pushforwardCompSymm, pushforwardCongr, id]
    exact Functor.sheafPushforwardContinuousComp'_assoc (Type u) _ _ _ _ _ _ _ _ _
  · have := C.isCocontinuous χ.op
    have := C.isCocontinuous ψ.op
    have := C.isCocontinuous φ.op
    have := C.isCocontinuous (χ ≫ ψ).op
    have := C.isCocontinuous (ψ ≫ φ).op
    have := C.isCocontinuous ((χ ≫ ψ) ≫ φ).op
    have := C.isCocontinuous (χ ≫ ψ ≫ φ).op
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map ψ.op).toFunctor
      (C.underlying.map χ.op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op m)))
      (topologyOfCoverings (C.coverage (Opposite.op l)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op k))))
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map φ.op).toFunctor
      (C.underlying.map ψ.op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op l))))
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map φ.op).toFunctor
      (C.underlying.map (χ ≫ ψ).op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op m)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op k))))
    have := CategoryTheory.isCocontinuous_comp (C.underlying.map (ψ ≫ φ).op).toFunctor
      (C.underlying.map χ.op).toFunctor (topologyOfCoverings (C.coverage (Opposite.op n)))
      (topologyOfCoverings (C.coverage (Opposite.op l)))
      (L := (topologyOfCoverings (C.coverage (Opposite.op k))))
    dsimp only [pushforwardCompSymm, pushforwardCongr, id, transitionMorphism, gStar]
    exact sheafPushforwardCocontinuousCompIso_assoc _ _ _ _ _ _ _ _ _

end SimplicialSiteSituation

end CategoryTheory

end
