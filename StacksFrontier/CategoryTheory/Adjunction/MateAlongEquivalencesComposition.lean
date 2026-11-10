module

public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import StacksFrontier.CategoryTheory.Adjunction.MateAlongEquivalences

/-!
# Mates along fully faithful functors: essential images and composition

## Main results

* `CategoryTheory.Adjunction.isIso_mateOfRightIso_app_of_mem_essImage`: if `G` and `H` are
  fully faithful, the mate is invertible at every object whose image under `G ⋙ L'` lies in the
  essential image of `H`.
* `CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app`: the mates are
  compatible with composition comparisons of the left adjoints, when the right adjoint
  comparisons are compatible with composition.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

section EssImage

variable {C : Type*} [Category* C] {D : Type*} [Category* D]
  {C' : Type*} [Category* C'] {D' : Type*} [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  (adj : L ⊣ R) (adj' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}

/-- **The mate is invertible at objects landing in the essential image.** If `G` and `H` are
fully faithful, the component at `X` of the mate of an isomorphism `R ⋙ G ≅ H ⋙ R'` is an
isomorphism as soon as its source `L' (G X)` lies in the essential image of `H`. -/
theorem isIso_mateOfRightIso_app_of_mem_essImage (e : R ⋙ G ≅ H ⋙ R') (hG : G.FullyFaithful)
    (hH : H.FullyFaithful) {X : C} (hX : H.essImage (L'.obj (G.obj X))) :
    IsIso ((mateOfRightIso adj adj' e).app X) := by
  obtain ⟨Z, ⟨i⟩⟩ := hX
  let θ := (mateOfRightIso adj adj' e).app X
  have hb : ∀ T : D, Function.Bijective (fun g : L.obj X ⟶ T => θ ≫ H.map g) := by
    intro T
    have h : (fun g : L.obj X ⟶ T => θ ≫ H.map g) =
        (adj'.homEquiv (G.obj X) (H.obj T)).symm ∘ (fun y => y ≫ e.hom.app T) ∘ G.map ∘
          (adj.homEquiv X T) := by
      funext g
      simpa only [Equiv.symm_apply_apply, Function.comp_apply, θ] using
        mateOfRightIso_app_comp_map_homEquiv_symm adj adj' e (adj.homEquiv X T g)
    have he : Function.Bijective (fun y : G.obj X ⟶ G.obj (R.obj T) =>
        y ≫ e.hom.app T) :=
      ⟨fun a b hab => by simpa using congrArg (· ≫ e.inv.app T) hab,
        fun y => ⟨y ≫ e.inv.app T, by simp⟩⟩
    rw [h]
    exact (adj'.homEquiv _ _).symm.bijective.comp (he.comp
        ((hG.map_bijective _ _).comp (adj.homEquiv X T).bijective))
  let φ : Z ⟶ L.obj X := hH.preimage (i.hom ≫ θ)
  have hφ : IsIso φ := by
    refine (isIso_iff_coyoneda_map_bijective _).mpr fun T => ?_
    have h : H.map ∘ (fun g : L.obj X ⟶ T => φ ≫ g) =
        (fun y => i.hom ≫ y) ∘ (fun g : L.obj X ⟶ T => θ ≫ H.map g) := by
      funext g
      simp only [Function.comp_apply, Functor.map_comp, φ, hH.map_preimage, Category.assoc]
    rw [← Function.Bijective.of_comp_iff' (hH.map_bijective _ _), h]
    have hi : Function.Bijective (fun y : L'.obj (G.obj X) ⟶ H.obj T => i.hom ≫ y) :=
      ⟨fun a b hab => by simpa using congrArg (i.inv ≫ ·) hab,
        fun y => ⟨i.inv ≫ y, by simp⟩⟩
    exact hi.comp (hb T)
  change IsIso θ
  rw [show θ = i.inv ≫ H.map φ by simp only [φ, hH.map_preimage, Iso.inv_hom_id_assoc]]
  infer_instance

end EssImage

section Composition

open TwoSquare

variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  [Category* D₀] [Category* D₁] [Category* D₂]
  {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₁ ⥤ C₂} {R₂ : C₂ ⥤ C₁} {L₁₂ : C₀ ⥤ C₂} {R₁₂ : C₂ ⥤ C₀}
  {L₁' : D₀ ⥤ D₁} {R₁' : D₁ ⥤ D₀} {L₂' : D₁ ⥤ D₂} {R₂' : D₂ ⥤ D₁} {L₁₂' : D₀ ⥤ D₂}
  {R₁₂' : D₂ ⥤ D₀}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₁₂ : L₁₂ ⊣ R₁₂)
  (b₁ : L₁' ⊣ R₁') (b₂ : L₂' ⊣ R₂') (b₁₂ : L₁₂' ⊣ R₁₂')
  {G₀ : C₀ ⥤ D₀} {G₁ : C₁ ⥤ D₁} {G₂ : C₂ ⥤ D₂}

/-- The conjugate of the composition comparison of left adjoints is the inverse of the
comparison of right adjoints. -/
private theorem conjugateEquiv_leftAdjointCompIso_hom_eq_inv (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (a₁₂ : L₁₂ ⊣ R₁₂) (c : R₂ ⋙ R₁ ≅ R₁₂) :
    conjugateEquiv a₁₂ (a₁.comp a₂) (leftAdjointCompIso a₁ a₂ a₁₂ c).hom = c.inv :=
  congrArg Iso.hom ((conjugateIsoEquiv a₁₂ (a₁.comp a₂)).apply_symm_apply c.symm)

/-- The mate of `mateOfRightIso` conjugates back to the original isomorphism. -/
private theorem mateEquiv_mk_mateOfRightIso {L : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {L' : D₀ ⥤ D₁}
    {R' : D₁ ⥤ D₀} {G : C₀ ⥤ D₀} {H : C₁ ⥤ D₁} (a : L ⊣ R) (b : L' ⊣ R') (e : R ⋙ G ≅ H ⋙ R') :
    mateEquiv a b (TwoSquare.mk _ _ _ _ (mateOfRightIso a b e)) = e.hom :=
  Equiv.apply_symm_apply _ _

/-- **Mates of right adjoint comparisons are compatible with composition.** Let `L₁ ⊣ R₁`,
`L₂ ⊣ R₂`, `L₁₂ ⊣ R₁₂` and `L₁' ⊣ R₁'`, `L₂' ⊣ R₂'`, `L₁₂' ⊣ R₁₂'` be adjunctions, `G₀`, `G₁`, `G₂`
functors and `e₁`, `e₂`, `e₁₂` isomorphisms between the composites of the right adjoints with them,
compatible with composition comparisons `c : R₂ ⋙ R₁ ≅ R₁₂` and `c' : R₂' ⋙ R₁' ≅ R₁₂'`. Then the
mates `G ⋙ L' ⟶ L ⋙ G` of the `e`'s are compatible with the induced composition comparisons of the
left adjoints. The comparison `ι` is any isomorphism equal to the one of `c`. -/
theorem leftAdjointCompIso_hom_app_comp_mateOfRightIso_app
    (e₁ : R₁ ⋙ G₀ ≅ G₁ ⋙ R₁') (e₂ : R₂ ⋙ G₁ ≅ G₂ ⋙ R₂') (e₁₂ : R₁₂ ⋙ G₀ ≅ G₂ ⋙ R₁₂')
    (c : R₂ ⋙ R₁ ≅ R₁₂) (c' : R₂' ⋙ R₁' ≅ R₁₂')
    (h : ∀ M, G₀.map (c.hom.app M) ≫ e₁₂.hom.app M =
      e₁.hom.app (R₂.obj M) ≫ R₁'.map (e₂.hom.app M) ≫ c'.hom.app (G₂.obj M))
    (ι : L₁ ⋙ L₂ ≅ L₁₂) (hι : ι = leftAdjointCompIso a₁ a₂ a₁₂ c) (N : C₀) :
    (leftAdjointCompIso b₁ b₂ b₁₂ c').hom.app (G₀.obj N) ≫ (mateOfRightIso a₁₂ b₁₂ e₁₂).app N =
      L₂'.map ((mateOfRightIso a₁ b₁ e₁).app N) ≫ (mateOfRightIso a₂ b₂ e₂).app (L₁.obj N) ≫
        G₂.map (ι.hom.app N) := by
  subst hι
  have key : (TwoSquare.mk _ _ _ _ (mateOfRightIso a₁₂ b₁₂ e₁₂)).whiskerRight
        (leftAdjointCompIso b₁ b₂ b₁₂ c').hom =
      ((TwoSquare.mk _ _ _ _ (mateOfRightIso a₁ b₁ e₁)) ≫ᵥ
        (TwoSquare.mk _ _ _ _ (mateOfRightIso a₂ b₂ e₂))).whiskerLeft
          (leftAdjointCompIso a₁ a₂ a₁₂ c).hom := by
    apply (mateEquiv a₁₂ (b₁.comp b₂)).injective
    rw [mateEquiv_conjugateEquiv_vcomp a₁₂ b₁₂ (b₁.comp b₂),
      conjugateEquiv_mateEquiv_vcomp a₁₂ (a₁.comp a₂) (b₁.comp b₂), mateEquiv_hcomp a₁ b₁ a₂ b₂]
    rw [mateEquiv_mk_mateOfRightIso, mateEquiv_mk_mateOfRightIso, mateEquiv_mk_mateOfRightIso,
      conjugateEquiv_leftAdjointCompIso_hom_eq_inv, conjugateEquiv_leftAdjointCompIso_hom_eq_inv]
    ext M
    simp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop, TwoSquare.hComp,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rw [← cancel_epi (G₀.map (c.hom.app M)), ← Category.assoc, h, ← G₀.map_comp_assoc,
      Iso.hom_inv_id_app, G₀.map_id, Category.id_comp]
    simp
  simpa [TwoSquare.vComp, mateOfRightIso] using congrArg (fun t => NatTrans.app t N) key

end Composition

end CategoryTheory.Adjunction

end
