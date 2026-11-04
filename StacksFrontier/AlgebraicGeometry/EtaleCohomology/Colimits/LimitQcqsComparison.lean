module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqs

/-!
# Stacks 09YQ for quasi-compact and quasi-separated levels: transfer to an open of the least stage

Transfer of the comparison of `colim_i Ext^m(f_i⁻¹Q, f_i⁻¹G)` with `Ext^m(f⁻¹Q, f⁻¹G)` from an
extension by zero `Q = j_!A` along an open immersion `j : W ⟶ X_⊥` to the restricted system
`(X_i ×_{X_⊥} W)`.

## Main definitions

* `transferMap`: The comparison map from the Ext groups of `Q` at a stage of the system to those
  of the pullback of `A` at the corresponding stage of the restricted system.
* `transferMapL`: The corresponding comparison map at the limit.

## Main results

* `good_of_restrict`: If `Q` is the extension by zero of `A`, the comparison for `Q` on the
  system is an isomorphism as soon as the comparison for the pullback of `A` is one on the
  restricted system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology.LimitExt

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

section Transfer

variable {J : Type u} [Preorder J] [OrderBot J] [IsDirected J (· ≤ ·)]
  {E : Jᵒᵖ ⥤ Scheme.{u}} {c : Cone E} {W : Scheme.{u}} (ι : W ⟶ E.obj (op ⊥))
  [IsOpenImmersion ι]

/-- The projection of a stage of the restricted system to `W` factors through the least stage
of the restricted system. -/
theorem rsnd_eq (i : J) : rsnd E ι i = toBot (restrictSystem E ι) i ≫ rsnd E ι ⊥ :=
  (restrictSystem_map_snd E ι _).symm

/-- The projection of the limit of the restricted system to `W` factors through the least stage
of the restricted system. -/
theorem rsndL_eq : rsndL E c ι = (restrictCone E ι c).π.app (op ⊥) ≫ rsnd E ι ⊥ :=
  (restrictCone_π_snd E c ι ⊥).symm

omit [IsOpenImmersion ι] in
/-- The projections of the restricted system to `W` commute with its transition maps. -/
theorem trans_rsnd {i i' : J} (h : i ≤ i') :
    rsnd E ι i' = trans (restrictSystem E ι) h ≫ rsnd E ι i :=
  (restrictSystem_map_snd E ι _).symm

omit [IsOpenImmersion ι] in
/-- The projections of the restricted system to the stages of the system commute with the
transition maps. -/
theorem trans_rfst {i i' : J} (h : i ≤ i') :
    trans (restrictSystem E ι) h ≫ rfst E ι i = rfst E ι i' ≫ trans E h :=
  restrictSystem_map_fst E ι _

/-- The comparison map from the theory of `Q` on the system to the theory of `s⁻¹A` on the
restricted system, at a stage. -/
def transferMap {Q G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q) (i : J) (m : ℕ) :=
  (conjBase (toBot (restrictSystem E ι) i) (rsnd E ι ⊥) (rsnd E ι i) (rsnd_eq ι i) A
      ((etaleAbelianInverseImage.{u, 0} ι).obj G) m).comp
    (restrictBase (G := G) ι (toBot E i) (rsnd E ι i) (rfst E ι i) (rsnd E ι i ≫ ι) rfl
      (rfst_toBot E ι i).symm η m)

/-- The comparison map at the limit. -/
def transferMapL {Q G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q) (m : ℕ) :=
  (conjBase ((restrictCone E ι c).π.app (op ⊥)) (rsnd E ι ⊥) (rsndL E c ι) (rsndL_eq ι) A
      ((etaleAbelianInverseImage.{u, 0} ι).obj G) m).comp
    (restrictBase (G := G) ι (c.π.app (op ⊥)) (rsndL E c ι) (rfstL E c ι) (rsndL E c ι ≫ ι) rfl
      (rfstL_cone E c ι).symm η m)

/-- The base change of `restrictBase` along a pullback square of an open immersion, followed by
`conjBase`, is bijective. -/
private theorem bijective_conjBase_comp_restrictBase {S W X W' Y : Scheme.{u}} (ι : W ⟶ S)
    [IsOpenImmersion ι] (g : X ⟶ S) (e : W' ⟶ W) (j' : W' ⟶ X) (sq : IsPullback j' e g ι)
    (y : W' ⟶ Y) (s : Y ⟶ W) (h : e = y ≫ s)
    {Q : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q)
    (hη : IsIso (((extAdj ι).homEquiv A Q).symm η)) (m : ℕ) :
    Function.Bijective
      ((conjBase y s e h A ((etaleAbelianInverseImage.{u, 0} ι).obj G) m).comp
        (restrictBase (G := G) ι g e j' (e ≫ ι) rfl sq.w.symm η m)) := by
  have : IsOpenImmersion j' := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    sq.flip inferInstance
  rw [AddMonoidHom.coe_comp]
  exact (conjBase_bijective _ _ _ _ _ _ m).comp (bijective_restrictBase ι g e j' sq G η hη m)

/-- If `η` corresponds to an isomorphism from the extension by zero of `A` to `Q`, then the
comparison map `transferMap` at each stage is bijective. -/
theorem transferMap_bijective {Q : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q)
    (hη : IsIso (((extAdj ι).homEquiv A Q).symm η)) (i : J) (m : ℕ) :
    Function.Bijective (transferMap (G := G) ι η i m) :=
  bijective_conjBase_comp_restrictBase ι (toBot E i) _ _ (IsPullback.of_hasPullback _ _) _ _
    (rsnd_eq ι i) G η hη m

/-- If `η` corresponds to an isomorphism from the extension by zero of `A` to `Q`, then the
comparison map `transferMapL` at the limit is injective. -/
theorem transferMapL_injective {Q : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    (G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q)
    (hη : IsIso (((extAdj ι).homEquiv A Q).symm η)) (m : ℕ) :
    Function.Injective (transferMapL (c := c) (G := G) ι η m) :=
  (bijective_conjBase_comp_restrictBase ι (c.π.app (op ⊥)) _ _ (IsPullback.of_hasPullback _ _)
    _ _ (rsndL_eq ι) G η hη m).1

/-- The comparison maps `transferMap` commute with the restriction maps `resK` along the
transition maps of the system and of the restricted system. -/
theorem transferMap_resK {Q G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q) {i i' : J} (h : i ≤ i') (m : ℕ) (x) :
    transferMap (G := G) ι η i' m (resK (trans E h) _ _ (toBot_eq E h) Q G m x) =
      resK (trans (restrictSystem E ι) h) _ _ (toBot_eq (restrictSystem E ι) h) _ _ m
        (transferMap (G := G) ι η i m x) := by
  simp only [transferMap, AddMonoidHom.comp_apply]
  rw [resK_conjBase (trans (restrictSystem E ι) h) (rsnd E ι ⊥) _ _ (toBot_eq _ h) _
    (rsnd_eq ι i) _ (rsnd_eq ι i') (trans_rsnd ι h),
    resK_restrictBase ι (toBot E i) (toBot E i') (trans E h) (toBot_eq E h)
    (rsnd E ι i) (rsnd E ι i') (trans (restrictSystem E ι) h) (trans_rsnd ι h)
    (rfst E ι i) (rfst E ι i') _ rfl (rfst_toBot E ι i).symm _ rfl (rfst_toBot E ι i').symm
    (trans (restrictSystem E ι) h ≫ rfst E ι i) rfl (trans_rfst ι h) η m x]

/-- The comparison map `transferMapL` at the limit is compatible with `transferMap` at a stage
through the restriction maps `resK` along the projections of the limit cones. -/
theorem transferMapL_resK {Q G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q) (i : J) (m : ℕ) (x) :
    transferMapL (c := c) (G := G) ι η m (resK (c.π.app (op i)) _ _ (cone_toBot E c i) Q G m x) =
      resK ((restrictCone E ι c).π.app (op i)) _ _
        (cone_toBot (restrictSystem E ι) (restrictCone E ι c) i) _ _ m
        (transferMap (G := G) ι η i m x) := by
  simp only [transferMap, transferMapL, AddMonoidHom.comp_apply]
  rw [resK_conjBase ((restrictCone E ι c).π.app (op i)) (rsnd E ι ⊥) _ _
    (cone_toBot (restrictSystem E ι) (restrictCone E ι c) i) _ (rsnd_eq ι i) _ (rsndL_eq ι)
    (restrictCone_π_snd E c ι i).symm,
    resK_restrictBase ι (toBot E i) (c.π.app (op ⊥)) (c.π.app (op i)) (cone_toBot E c i)
    (rsnd E ι i) (rsndL E c ι) ((restrictCone E ι c).π.app (op i))
    (restrictCone_π_snd E c ι i).symm
    (rfst E ι i) (rfstL E c ι) _ rfl (rfst_toBot E ι i).symm _ rfl (rfstL_cone E c ι).symm
    ((restrictCone E ι c).π.app (op i) ≫ rfst E ι i) rfl (restrictCone_π_fst E c ι i) η m x]

/-- **Transfer to an open of the least stage.** If `Q` on `X_⊥` is the extension by zero of `A`
on an open `W` (through `η`), then the comparison for `Q` on the system `(X_i)` is an isomorphism
as soon as the comparison for `A`, pulled back, is one on the system `(X_i ×_{X_⊥} W)`. -/
theorem good_of_restrict {Q G : Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}}
    {A : Sheaf W.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (η : A ⟶ (etaleAbelianInverseImage.{u, 0} ι).obj Q)
    (hη : IsIso (((extAdj ι).homEquiv A Q).symm η))
    (hW : Good (restrictSystem E ι) (restrictCone E ι c)
      ((etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥)).obj A)
      ((etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥)).obj
        ((etaleAbelianInverseImage.{u, 0} ι).obj G))) :
    Good E c Q G := by
  have h₁ : ∀ i : J, (invBot (restrictSystem E ι) i).Additive :=
    fun i => invBot_additive (restrictSystem E ι) i
  have h₂ : ∀ i : J, PreservesFiniteLimits (invBot (restrictSystem E ι) i) :=
    fun i => invBot_preservesFiniteLimits (restrictSystem E ι) i
  have h₃ : ∀ i : J, PreservesFiniteColimits (invBot (restrictSystem E ι) i) :=
    fun i => invBot_preservesFiniteColimits (restrictSystem E ι) i
  have h₄ := invLim_additive (restrictSystem E ι) (restrictCone E ι c)
  have h₅ := invLim_preservesFiniteLimits (restrictSystem E ι) (restrictCone E ι c)
  have h₆ := invLim_preservesFiniteColimits (restrictSystem E ι) (restrictCone E ι c)
  exact Stacks.ExtDirectedSystem.good_of_bijective.{u + 1, u + 1, u + 1, u + 1, u + 2, u + 2,
      u + 2, u}
    (J := J)
    (𝒜 := Sheaf (E.obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1}) (𝒞 := ShE E)
    (𝒞L := Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P := invBot E) (PL := invLim E c) (G := G)
    (τ := fun h M m => resK (trans E h) _ _ (toBot_eq E h) M G m)
    (lm := fun i M m => resK (c.π.app (op i)) _ _ (cone_toBot E c i) M G m)
    (𝒜' := Sheaf ((restrictSystem E ι).obj (op ⊥)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (𝒞' := ShE (restrictSystem E ι))
    (𝒞L' := Sheaf (restrictCone E ι c).pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (P' := invBot (restrictSystem E ι)) (PL' := invLim (restrictSystem E ι) (restrictCone E ι c))
    (G' := (etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥)).obj
      ((etaleAbelianInverseImage.{u, 0} ι).obj G))
    (τ' := fun h M m => resK (trans (restrictSystem E ι) h) _ _ (toBot_eq (restrictSystem E ι) h) M
      _ m)
    (lm' := fun i M m => resK ((restrictCone E ι c).π.app (op i)) _ _
      (cone_toBot (restrictSystem E ι) (restrictCone E ι c) i) M _ m)
    (M := Q) (M' := (etaleAbelianInverseImage.{u, 0} (rsnd E ι ⊥)).obj A)
    (fun i m => transferMap (G := G) ι η i m) (fun m => transferMapL (c := c) (G := G) ι η m)
    (fun i m => transferMap_bijective ι G η hη i m) (fun m => transferMapL_injective ι G η hη m)
    (fun h m x => transferMap_resK ι η h m x) (fun i m x => transferMapL_resK ι η i m x) hW

end Transfer

end Stacks.EtaleCohomology.LimitExt
