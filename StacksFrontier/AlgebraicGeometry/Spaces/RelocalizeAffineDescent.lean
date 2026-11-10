module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeRestrict
public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEffectiveDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme

/-!
# Affineness through the lower-shriek extension to a smaller base

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `Λ` be the lower-shriek extension
`CategoryTheory.OverShriek.relocalizePresheafFunctor g` from presheaves on the big fppf site of `S`
to presheaves on that of `S'` (Stacks 03I5). This file proves two general facts about `Λ` and
combines them with effective descent of affine morphisms along surjective étale morphisms.

* A presheaf `F` on `C/A` whose extension `Λ F` is representable by `Y` is itself representable,
  by `Y` with the factorization through `A` that the identification carries
  (`CategoryTheory.OverShriek.exists_iso_yoneda_of_relocalize_iso`).
* The projection formula `Λ (F ×_{j⁻¹ Y} j⁻¹ Y') = Λ F ×_Y Y'` for a morphism `e : Y' ⟶ Y` of
  presheaves on `C/X`, with the maps to `Y` and `Y'` transposed across `Λ ⊣ j⁻¹`
  (`CategoryTheory.OverShriek.isPullback_relocalizeOfRestricted`).
* `AlgebraicGeometry.Space.isAffineSpace_of_isPullback_relocalize`: an fppf sheaf `F` over `S`
  whose extension sits in a cartesian square over a surjective étale morphism `c ⟶ a` of affine
  objects of the site of `S'`, with affine upper left corner, is an affine algebraic space over
  `S`.

## Implementation notes

The last statement is the form in which affineness of an algebraic space over an arbitrary base
`S` is read off a morphism to an affine scheme *over `Spec ℤ`*: over a non-separated `S` an affine
scheme need not be affine over `S × Spec P`, so the descent is carried out over the terminal
scheme, where `Spec P` is an affine object of the site, and transported back by the first fact.
The descent itself is `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X)

/-- Under an identification `e : Λ F ≅ h_Y`, the factorization through `A` carried by the
section of `Λ F` corresponding to `t : W ⟶ Y` is `t` followed by the factorization of `Y`
itself. -/
theorem relocalizeToYoneda_iso_inv {F : (Over A)ᵒᵖ ⥤ Type v} {Y : Over X}
    (e : (relocalizePresheafFunctor a).obj F ≅ yoneda.obj Y) (W : Over X) (t : W ⟶ Y) :
    (relocalizeToYoneda a F).app (op W) (e.inv.app (op W) t) =
      t ≫ (relocalizeToYoneda a F).app (op Y) (e.inv.app (op Y) (𝟙 Y)) := by
  have h1 := NatTrans.naturality_apply e.inv t.op (𝟙 Y)
  have h2 := NatTrans.naturality_apply (relocalizeToYoneda a F) t.op
    (e.inv.app (op Y) (𝟙 Y))
  simp only [yoneda_obj_map, unop_op, Quiver.Hom.unop_op, Category.comp_id,
    TypeCat.ofHom_apply] at h1 h2
  rw [h1, h2]

/-- **A presheaf on `C/A` whose relocalization to `C/X` is representable is representable**, by
an object of `C/A` with the same underlying object of `C`. The representing object lies over `A`
through the factorization that the identification `Λ F ≅ h_Y` carries. -/
theorem exists_iso_yoneda_of_relocalize_iso {F : (Over A)ᵒᵖ ⥤ Type v} {Y : Over X}
    (e : (relocalizePresheafFunctor a).obj F ≅ yoneda.obj Y) :
    ∃ T : Over A, T.left = Y.left ∧ Nonempty (F ≅ yoneda.obj T) := by
  set y : Y ⟶ Over.mk a := (relocalizeToYoneda a F).app (op Y) (e.inv.app (op Y) (𝟙 Y)) with hy
  have hρ : ∀ (W : Over X) (t : W ⟶ Y),
      (relocalizeToYoneda a F).app (op W) (e.inv.app (op W) t) = t ≫ y :=
    relocalizeToYoneda_iso_inv a e
  -- the tautological section of `Λ F` attached to a section of `F`
  let z₀ : ∀ (W : Over A), F.obj (op W) →
      ((relocalizePresheafFunctor a).obj F).obj (op ((Over.map a).obj W)) :=
    fun W x => ⟨⟨W.hom, x⟩, rfl⟩
  have hz₀ : ∀ (W : Over A) (x : F.obj (op W)),
      (e.hom.app (op ((Over.map a).obj W)) (z₀ W x)).left ≫ y.left = W.hom := by
    intro W x
    have h := hρ _ (e.hom.app _ (z₀ W x))
    rw [Iso.hom_inv_id_app_apply] at h
    exact (congrArg Over.Hom.left h).symm
  -- the section of `Λ F` attached to a morphism to `Over.mk y.left`
  let t₀ : ∀ (W : Over A), (W ⟶ Over.mk y.left) → ((Over.map a).obj W ⟶ Y) :=
    fun W m => Over.homMk m.left (by
      have h1 := Over.w m
      have h2 := Over.w y
      simp only [Over.mk_left, Over.mk_hom] at h1 h2
      simp [← h1, ← h2])
  have ht₀ : ∀ (W : Over A) (m : W ⟶ Over.mk y.left),
      (e.inv.app (op ((Over.map a).obj W)) (t₀ W m)).1.1 = W.hom := by
    intro W m
    refine (congrArg Over.Hom.left (hρ _ (t₀ W m))).trans ?_
    simpa [t₀] using Over.w m
  let back : ∀ (W : Over A) (z : ((relocalizePresheafFunctor a).obj F).obj
      (op ((Over.map a).obj W))), z.1.1 = W.hom → F.obj (op W) :=
    fun W z hz => F.map (Over.homMk (𝟙 W.left) (by simpa using hz) :
      W ⟶ Over.mk z.1.1).op z.1.2
  have hback : ∀ (W : Over A) (x : F.obj (op W)) (z) (hz : z.1.1 = W.hom),
      z = z₀ W x → back W z hz = x := by
    rintro W x z hz rfl
    simp only [back]
    have hid : (Over.homMk (𝟙 W.left) (by simpa using hz) : W ⟶ Over.mk (z₀ W x).1.1) =
        𝟙 W := by ext; simp
    rw [hid, op_id]
    exact Functor.map_id_apply F _ _
  have hz₀back : ∀ (W : Over A) (z) (hz : z.1.1 = W.hom), z₀ W (back W z hz) = z :=
    fun W z hz => Subtype.ext (sigmaMk_eq_self F z.1.2 _ rfl)
  refine ⟨Over.mk y.left, rfl, ⟨NatIso.ofComponents (fun W => Equiv.toIso
    { toFun := fun x => Over.homMk (e.hom.app (op ((Over.map a).obj W.unop)) (z₀ W.unop x)).left
        (hz₀ W.unop x)
      invFun := fun m => back W.unop _ (ht₀ W.unop m)
      left_inv := fun x => by
        dsimp only
        refine hback W.unop x _ (ht₀ W.unop _) ?_
        have : t₀ W.unop (Over.homMk (e.hom.app (op ((Over.map a).obj W.unop))
            (z₀ W.unop x)).left (hz₀ W.unop x)) = e.hom.app _ (z₀ W.unop x) :=
          Over.OverMorphism.ext rfl
        rw [this, Iso.hom_inv_id_app_apply]
      right_inv := fun m => by
        apply Over.OverMorphism.ext
        change (e.hom.app _ (z₀ W.unop (back W.unop _ (ht₀ W.unop m)))).left = m.left
        rw [hz₀back W.unop _ (ht₀ W.unop m), Iso.inv_hom_id_app_apply]
        rfl }) (fun {W W'} f => by
      ext x
      apply Over.OverMorphism.ext
      change (e.hom.app _ (z₀ W'.unop (F.map f x))).left =
        f.unop.left ≫ (e.hom.app _ (z₀ W.unop x)).left
      have hz : z₀ W'.unop (F.map f x) =
          ((relocalizePresheafFunctor a).obj F).map ((Over.map a).map f.unop).op
            (z₀ W.unop x) :=
        Subtype.ext <| sigmaMk_eq F x f.unop
          (Over.homMk f.unop.left rfl : Over.mk (f.unop.left ≫ W.unop.hom) ⟶ Over.mk W.unop.hom)
          rfl
      rw [hz, NatTrans.naturality_apply]
      rfl)⟩⟩

/-- `Λ` acts on sections by keeping the factorization and applying the morphism to the section. -/
theorem relocalize_map_app_apply {F F' : (Over A)ᵒᵖ ⥤ Type v} (k : F ⟶ F') {W : (Over X)ᵒᵖ}
    (ψ : W.unop.left ⟶ A) (s : F.obj (op (Over.mk ψ))) (h : ψ ≫ a = W.unop.hom) :
    ((relocalizePresheafFunctor a).map k).app W ⟨⟨ψ, s⟩, h⟩ = ⟨⟨ψ, k.app _ s⟩, h⟩ :=
  rfl

/-- The transpose of `β : G ⟶ j^{-1}F` evaluated on a section `(ψ, s)` of `Λ G` over `W`. -/
theorem relocalizeOfRestricted_app_apply {G : (Over A)ᵒᵖ ⥤ Type v} {F : (Over X)ᵒᵖ ⥤ Type v}
    (β : G ⟶ (relocalizeRestrict a).obj F) {W : (Over X)ᵒᵖ}
    (ψ : W.unop.left ⟶ A) (s : G.obj (op (Over.mk ψ))) (h : ψ ≫ a = W.unop.hom) :
    (relocalizeOfRestricted a β).app W ⟨⟨ψ, s⟩, h⟩ =
      F.map (Over.homMk (𝟙 W.unop.left) (by rw [Category.id_comp]; exact h) :
        W.unop ⟶ Over.mk (ψ ≫ a)).op (β.app (op (Over.mk ψ)) s) :=
  rfl

/-- **Projection formula for the lower-shriek extension.** A cartesian square of presheaves on
`C/A` over the restriction `j^{-1}e` of a morphism `e : Y' ⟶ Y` of presheaves on `C/X` becomes,
after `Λ` and transposition across the adjunction `Λ ⊣ j^{-1}`, a cartesian square over `e`:
`Λ(F ×_{j^{-1}Y} j^{-1}Y') = ΛF ×_Y Y'`. -/
theorem isPullback_relocalizeOfRestricted {P F : (Over A)ᵒᵖ ⥤ Type v}
    {Y Y' : (Over X)ᵒᵖ ⥤ Type v} {top : P ⟶ (relocalizeRestrict a).obj Y'} {left : P ⟶ F}
    {ψ : F ⟶ (relocalizeRestrict a).obj Y} {e : Y' ⟶ Y}
    (h : IsPullback top left ((relocalizeRestrict a).map e) ψ) :
    IsPullback (relocalizeOfRestricted a top) ((relocalizePresheafFunctor a).map left) e
      (relocalizeOfRestricted a ψ) := by
  refine IsPullback.of_forall_isPullback_app fun W => ?_
  -- the identification of `W` with `j (W.left, ψ₀)` and its inverse
  let m : ∀ (ψ₀ : W.unop.left ⟶ A), ψ₀ ≫ a = W.unop.hom → (W.unop ⟶ Over.mk (ψ₀ ≫ a)) :=
    fun ψ₀ h₀ => Over.homMk (𝟙 W.unop.left) (by rw [Category.id_comp]; exact h₀)
  let m' : ∀ (ψ₀ : W.unop.left ⟶ A), ψ₀ ≫ a = W.unop.hom → (Over.mk (ψ₀ ≫ a) ⟶ W.unop) :=
    fun ψ₀ h₀ => Over.homMk (𝟙 W.unop.left) (by simpa using h₀.symm)
  have hmm' : ∀ ψ₀ h₀, m ψ₀ h₀ ≫ m' ψ₀ h₀ = 𝟙 _ := fun _ _ => by ext; simp [m, m']
  have hm'm : ∀ ψ₀ h₀, m' ψ₀ h₀ ≫ m ψ₀ h₀ = 𝟙 _ := fun _ _ => by ext; simp [m, m']
  have hpt : ∀ O : Over A, IsPullback (top.app (op O)) (left.app (op O))
      (e.app (op ((Over.map a).obj O))) (ψ.app (op O)) := fun O => h.app (op O)
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    obtain ⟨⟨ψ₀, p⟩, h₀⟩ := x
    replace h₀ : ψ₀ ≫ a = W.unop.hom := h₀
    change e.app W (Y'.map (m ψ₀ h₀).op (top.app _ p)) =
      Y.map (m ψ₀ h₀).op (ψ.app _ (left.app _ p))
    rw [NatTrans.naturality_apply]
    congr 1
    exact ConcreteCategory.congr_hom (hpt (Over.mk ψ₀)).w p
  · rintro ⟨⟨ψ₁, p₁⟩, h₁⟩ ⟨⟨ψ₂, p₂⟩, h₂⟩ ⟨ht, hl⟩
    replace h₁ : ψ₁ ≫ a = W.unop.hom := h₁
    replace h₂ : ψ₂ ≫ a = W.unop.hom := h₂
    change Y'.map (m ψ₁ h₁).op (top.app _ p₁) = Y'.map (m ψ₂ h₂).op (top.app _ p₂) at ht
    have hl₀ : (⟨ψ₁, left.app _ p₁⟩ : Σ χ : W.unop.left ⟶ A, F.obj (op (Over.mk χ))) =
        ⟨ψ₂, left.app _ p₂⟩ := congrArg Subtype.val hl
    obtain ⟨hψ, hl''⟩ := Sigma.mk.inj_iff.mp hl₀
    subst hψ
    have hl' : left.app _ p₁ = left.app _ p₂ := eq_of_heq hl''
    have ht' : top.app _ p₁ = top.app _ p₂ := by
      have := congrArg (Y'.map (m' ψ₁ h₁).op) ht
      rwa [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp,
        hm'm ψ₁ h₁, op_id, Functor.map_id_apply, Functor.map_id_apply] at this
    have := Types.ext_of_isPullback (hpt (Over.mk ψ₁)) ht' hl'
    subst this
    rfl
  · rintro x₂ ⟨⟨ψ₀, f⟩, h₀⟩ hx
    replace h₀ : ψ₀ ≫ a = W.unop.hom := h₀
    change e.app W x₂ = Y.map (m ψ₀ h₀).op (ψ.app _ f) at hx
    obtain ⟨p, hp₁, hp₂⟩ := Types.exists_of_isPullback (hpt (Over.mk ψ₀))
      (Y'.map (m' ψ₀ h₀).op x₂) f (by
        change e.app _ (Y'.map (m' ψ₀ h₀).op x₂) = ψ.app _ f
        rw [NatTrans.naturality_apply, hx, ← Functor.map_comp_apply, ← op_comp,
          hm'm ψ₀ h₀, op_id, Functor.map_id_apply])
    refine ⟨⟨⟨ψ₀, p⟩, h₀⟩, ?_, ?_⟩
    · change Y'.map (m ψ₀ h₀).op (top.app _ p) = x₂
      rw [hp₁, ← Functor.map_comp_apply, ← op_comp, hmm' ψ₀ h₀, op_id,
        Functor.map_id_apply]
    · change (⟨⟨ψ₀, left.app _ p⟩, h₀⟩ : ((relocalizePresheafFunctor a).obj F).obj W) = _
      rw [hp₂]

end CategoryTheory.OverShriek

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
  (g : B.obj hS ⟶ B.obj hS')

/-- **An fppf sheaf over `S` whose lower-shriek extension along `g : S ⟶ S'` is cartesian over a
surjective étale morphism of affine objects of the site of `S'`, with affine source, is an affine
algebraic space over `S`.**

The extension `Λ F` receives the map `f` to the affine object `a`, and its base change along the
surjective étale `q : c ⟶ a` is the affine `v`. Affine morphisms descend effectively along
surjective étale morphisms of the big fppf site of `S'`
(`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`), so `Λ F` is
represented by an object affine over `a`, hence affine; and a presheaf whose lower-shriek
extension is represented by an object is represented over `S` by the same scheme
(`CategoryTheory.OverShriek.exists_iso_yoneda_of_relocalize_iso`). -/
theorem isAffineSpace_of_isPullback_relocalize {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    {a c v : BigFppfOver B S' hS'} (ha : IsAffine ((BigFppfOver.toScheme B S' hS').obj a))
    (hc : IsAffine ((BigFppfOver.toScheme B S' hS').obj c))
    (hv : IsAffine ((BigFppfOver.toScheme B S' hS').obj v))
    (q : c ⟶ a) (hqs : Surjective ((BigFppfOver.toScheme B S' hS').map q))
    (hqe : Etale ((BigFppfOver.toScheme B S' hS').map q))
    (f : (OverShriek.relocalizePresheafFunctor g).obj F ⟶ yoneda.obj a)
    (m : yoneda.obj v ⟶ (OverShriek.relocalizePresheafFunctor g).obj F) (r : v ⟶ c)
    (sq : IsPullback m (yoneda.map r) f (yoneda.map q)) :
    IsAffineSpace B S hS F := by
  have hFs : Presheaf.IsSheaf (BigFppfOver.topology B S' hS')
      ((OverShriek.relocalizePresheafFunctor g).obj F) :=
    isSheaf_relocalize B (B.obj hS) (B.obj hS') g F hF
  have hYs : Presheaf.IsSheaf (BigFppfOver.topology B S' hS') (yoneda.obj a) :=
    (isSheaf_iff_isSheaf_of_type _ _).2 (BigFppfOver.isSheaf_of_type_yoneda_obj a)
  have hr : (MorphismProperty.inverseImage (@AlgebraicGeometry.IsAffineHom.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf (yoneda.map r) :=
    (presheaf_yoneda_map_iff B S' hS' (P := @AlgebraicGeometry.IsAffineHom.{u})
      inferInstance r).2 inferInstance
  have sq' : IsPullback m (yoneda.map r) f (yoneda.map q ≫ 𝟙 (yoneda.obj a)) := by
    rwa [Category.comp_id]
  have hres := isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S' hS' f hFs hYs
    (𝟙 (yoneda.obj a)) q hqs hqe m (yoneda.map r) sq' hr
  -- the base change along the identity of `yoneda.obj a`
  set Y := hres.rep.pullback (𝟙 (yoneda.obj a))
  have hpb := hres.rep.isPullback (𝟙 (yoneda.obj a))
  have hYa : AlgebraicGeometry.IsAffineHom
      ((BigFppfOver.toScheme B S' hS').map (hres.rep.snd (𝟙 (yoneda.obj a)))) :=
    hres.property_snd _
  have hY : IsAffine ((BigFppfOver.toScheme B S' hS').obj Y) :=
    isAffine_of_isAffineHom ((BigFppfOver.toScheme B S' hS').map (hres.rep.snd _))
  have h1 : IsIso (hres.rep.fst (𝟙 (yoneda.obj a))) := hpb.isIso_fst_of_isIso
  have h2 : IsIso (pullback.fst f (𝟙 (yoneda.obj a))) :=
    (IsPullback.of_hasPullback f (𝟙 _)).isIso_fst_of_isIso
  obtain ⟨T, hT, ⟨eT⟩⟩ := OverShriek.exists_iso_yoneda_of_relocalize_iso g
    ((asIso (hres.rep.fst (𝟙 (yoneda.obj a)) ≫ pullback.fst f (𝟙 _))).symm)
  refine ⟨T, ?_, ⟨eT⟩⟩
  change IsAffine (B.inclusion.obj T.left)
  rw [hT]
  exact hY

end AlgebraicGeometry.Space

end
