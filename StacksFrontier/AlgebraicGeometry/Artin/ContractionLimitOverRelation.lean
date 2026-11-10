module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionLimitSpaceModel
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Étale equivalence relations over an object of the site, and kernel pairs of étale atlases

Schemes over the underlying scheme of an object `V` of the big fppf site of `S` which lie in the
site are objects of the site over `V` (`AlgebraicGeometry.Space.overSiteObj`). An étale
equivalence relation of such schemes over `V`, given by jointly monic étale projections and
witnesses, has an algebraic space quotient over `V`
(`AlgebraicGeometry.Space.exists_quotient_of_overRelation`, from
`AlgebraicGeometry.Space.exists_quotient_of_witnesses`). Conversely, the kernel pair of an étale
atlas of a sheaf has étale projections and reflexivity, symmetry and transitivity witnesses, and
is closed in `N ×_V N` when the sheaf is separated over `V`.

These are steps of the descent of a separated algebraic space of finite presentation along a limit
of affine schemes in the proof of Stacks 0GI5.

## Main results

* `AlgebraicGeometry.Space.exists_quotient_of_overRelation`: the quotient over `V`.
* `AlgebraicGeometry.Space.etale_kernelPair`, `AlgebraicGeometry.Space.exists_refl_kernelPair`,
  `AlgebraicGeometry.Space.exists_symm_kernelPair`,
  `AlgebraicGeometry.Space.exists_trans_kernelPair`: the kernel pair of an étale atlas.
* `AlgebraicGeometry.Space.isClosedImmersion_lift_kernelPair`: closedness of the kernel pair of
  an étale atlas of a separated space.

## References

* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 0GI5](https://stacks.math.columbia.edu/tag/0GI5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.Groupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Schemes over an object of the site, as objects of the site -/

section OverSite

variable {B S hS} {V : BigFppfOver B S hS}

/-- A scheme over the underlying scheme of an object `V` of the site, contained in the site, as an
object of the site. -/
noncomputable def overSiteObj (X : Over ((BigFppfOver.toScheme B S hS).obj V))
    (hX : B.Contains X.left) : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS hX (X.hom ≫ B.inclusion.map V.hom)

/-- A morphism of schemes over `V`, as a morphism of the site. -/
noncomputable def overSiteHom {X Y : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hX : B.Contains X.left) (hY : B.Contains Y.left) (f : X ⟶ Y) :
    overSiteObj X hX ⟶ overSiteObj Y hY :=
  BigFppfOver.homMk B S hS hY _ f.left (by
    change f.left ≫ Y.hom ≫ B.inclusion.map V.hom = X.hom ≫ B.inclusion.map V.hom
    rw [← Category.assoc, Over.w f])

/-- The structure morphism to `V`, as a morphism of the site. -/
noncomputable def overSiteToBase (X : Over ((BigFppfOver.toScheme B S hS).obj V))
    (hX : B.Contains X.left) : overSiteObj X hX ⟶ V :=
  Over.homMk (ObjectProperty.homMk X.hom) (by apply ObjectProperty.hom_ext; rfl)

/-- The underlying morphism of schemes of `overSiteHom hX hY f` is `f.left`. -/
@[simp]
theorem toScheme_map_overSiteHom {X Y : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hX : B.Contains X.left) (hY : B.Contains Y.left) (f : X ⟶ Y) :
    (BigFppfOver.toScheme B S hS).map (overSiteHom hX hY f) = f.left := rfl

/-- The morphism of schemes underlying `overSiteToBase X hX` is the structure morphism of `X`. -/
@[simp]
theorem toScheme_map_overSiteToBase (X : Over ((BigFppfOver.toScheme B S hS).obj V))
    (hX : B.Contains X.left) :
    (BigFppfOver.toScheme B S hS).map (overSiteToBase X hX) = X.hom := rfl

/-- `overSiteHom` is compatible with composition. -/
theorem overSiteHom_comp {X Y Z : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hX : B.Contains X.left) (hY : B.Contains Y.left) (hZ : B.Contains Z.left) (f : X ⟶ Y)
    (g : Y ⟶ Z) : overSiteHom hX hY f ≫ overSiteHom hY hZ g = overSiteHom hX hZ (f ≫ g) :=
  BigFppfOver.map_toScheme_injective B S hS rfl

/-- `overSiteHom` sends the identity to the identity. -/
theorem overSiteHom_id {X : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hX : B.Contains X.left) : overSiteHom hX hX (𝟙 X) = 𝟙 _ :=
  BigFppfOver.map_toScheme_injective B S hS rfl

/-- `overSiteHom hX hY f` commutes with the structure morphisms to `V`. -/
theorem overSiteHom_comp_overSiteToBase {X Y : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hX : B.Contains X.left) (hY : B.Contains Y.left) (f : X ⟶ Y) :
    overSiteHom hX hY f ≫ overSiteToBase Y hY = overSiteToBase X hX :=
  BigFppfOver.map_toScheme_injective B S hS (Over.w f)

/-- The images in schemes over `S` of jointly monic morphisms of schemes over `V` are jointly
monic. -/
theorem jointlyMono₂_post_overSiteHom {N R : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hN : B.Contains N.left) (hR : B.Contains R.left) (sR tR : R ⟶ N)
    (hjm : ∀ {W : Over ((BigFppfOver.toScheme B S hS).obj V)} (x y : W ⟶ R),
      x ≫ sR = y ≫ sR → x ≫ tR = y ≫ tR → x = y) :
    JointlyMono₂ ((Over.post (X := B.obj hS) B.inclusion).map (overSiteHom hR hN sR))
      ((Over.post (X := B.obj hS) B.inclusion).map (overSiteHom hR hN tR)) := by
  refine ⟨fun {W} x y h₁ h₂ => ?_⟩
  let x₀ : W.left ⟶ R.left := x.left
  let y₀ : W.left ⟶ R.left := y.left
  have e₁ : x₀ ≫ sR.left = y₀ ≫ sR.left := congrArg CommaMorphism.left h₁
  have e₂ : x₀ ≫ tR.left = y₀ ≫ tR.left := congrArg CommaMorphism.left h₂
  let W' : Over ((BigFppfOver.toScheme B S hS).obj V) := Over.mk (x₀ ≫ R.hom)
  have hy : y₀ ≫ R.hom = x₀ ≫ R.hom := by
    rw [← Over.w sR, ← Category.assoc, ← Category.assoc, e₁]
  have := hjm (W := W') (Over.homMk x₀ rfl) (Over.homMk y₀ hy)
    (Over.OverMorphism.ext e₁) (Over.OverMorphism.ext e₂)
  exact Over.OverMorphism.ext (congrArg (fun m : W' ⟶ R => m.left) this)

/-- A transitivity witness on the fibre product of schemes over `V` gives one on the fibre product
in the site. -/
theorem exists_trans_overSiteHom {N R : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hN : B.Contains N.left) (hR : B.Contains R.left) (sR tR : R ⟶ N)
    (comp : pullback tR sR ⟶ R) (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR) :
    ∃ c : pullback (overSiteHom hR hN tR) (overSiteHom hR hN sR) ⟶ overSiteObj R hR,
      c ≫ overSiteHom hR hN sR =
          pullback.fst (overSiteHom hR hN tR) (overSiteHom hR hN sR) ≫ overSiteHom hR hN sR ∧
        c ≫ overSiteHom hR hN tR =
          pullback.snd (overSiteHom hR hN tR) (overSiteHom hR hN sR) ≫ overSiteHom hR hN tR := by
  let Tf := BigFppfOver.toScheme B S hS
  let sR' := overSiteHom hR hN sR
  let tR' := overSiteHom hR hN tR
  have hPS : IsPullback (pullback.fst tR sR).left (pullback.snd tR sR).left tR.left sR.left :=
    (IsPullback.of_hasPullback tR sR).map (Over.forget _)
  let φ : Tf.obj (pullback tR' sR') ⟶ (pullback tR sR).left :=
    hPS.lift (Tf.map (pullback.fst tR' sR')) (Tf.map (pullback.snd tR' sR')) (by
      have h := Tf.congr_map (pullback.condition (f := tR') (g := sR'))
      rw [Tf.map_comp, Tf.map_comp] at h
      exact h)
  have hφ₁ : φ ≫ (pullback.fst tR sR).left = Tf.map (pullback.fst tR' sR') := hPS.lift_fst _ _ _
  have hφ₂ : φ ≫ (pullback.snd tR sR).left = Tf.map (pullback.snd tR' sR') := hPS.lift_snd _ _ _
  let comp' : pullback tR' sR' ⟶ overSiteObj R hR :=
    BigFppfOver.homMk B S hS hR _ (φ ≫ comp.left) (by
      change (φ ≫ comp.left) ≫ R.hom ≫ B.inclusion.map V.hom = _
      rw [Category.assoc, ← Category.assoc comp.left, Over.w comp, ← Over.w (pullback.fst tR sR),
        ← Category.assoc, ← Category.assoc, hφ₁]
      exact (Category.assoc _ _ _).trans ((B.inclusion.map_comp _ _).symm.trans
        (congrArg B.inclusion.map (Over.w (pullback.fst tR' sR')))))
  refine ⟨comp', ?_, ?_⟩
  · apply BigFppfOver.map_toScheme_injective B S hS
    change (φ ≫ comp.left) ≫ sR.left = Tf.map (pullback.fst tR' sR') ≫ sR.left
    rw [Category.assoc, ← Over.comp_left, hcomp₁, Over.comp_left, ← Category.assoc, hφ₁]
    rfl
  · apply BigFppfOver.map_toScheme_injective B S hS
    change (φ ≫ comp.left) ≫ tR.left = Tf.map (pullback.snd tR' sR') ≫ tR.left
    rw [Category.assoc, ← Over.comp_left, hcomp₂, Over.comp_left, ← Category.assoc, hφ₂]
    rfl

/-- **The quotient of an étale equivalence relation of schemes over `V`.** An étale equivalence
relation `s, t : R ⟶ N` in schemes over the underlying scheme of `V`, given by jointly monic
étale projections and witnesses, with `N` and `R` in the site, has an algebraic space quotient
over `V`: a surjective étale atlas from `N` with kernel pair `R`, and a morphism to `V` restricting
to the structure morphism of `N`. -/
theorem exists_quotient_of_overRelation {N R : Over ((BigFppfOver.toScheme B S hS).obj V)}
    (hN : B.Contains N.left) (hR : B.Contains R.left) (sR tR : R ⟶ N) (hsE : Etale sR.left)
    (htE : Etale tR.left)
    (hjm : ∀ {W : Over ((BigFppfOver.toScheme B S hS).obj V)} (x y : W ⟶ R),
      x ≫ sR = y ≫ sR → x ≫ tR = y ≫ tR → x = y)
    (refl : N ⟶ R) (hrefl₁ : refl ≫ sR = 𝟙 N) (hrefl₂ : refl ≫ tR = 𝟙 N)
    (symm : R ⟶ R) (hsymm₁ : symm ≫ sR = tR) (hsymm₂ : symm ≫ tR = sR)
    (comp : pullback tR sR ⟶ R)
    (hcomp₁ : comp ≫ sR = pullback.fst tR sR ≫ sR)
    (hcomp₂ : comp ≫ tR = pullback.snd tR sR ≫ tR) :
    ∃ (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS X)
      (q : yoneda.obj (overSiteObj N hN) ⟶ X) (p : X ⟶ yoneda.obj V),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf q ∧
      IsPullback (yoneda.map (overSiteHom hR hN sR)) (yoneda.map (overSiteHom hR hN tR)) q q ∧
      q ≫ p = yoneda.map (overSiteToBase N hN) := by
  let sR' := overSiteHom hR hN sR
  let tR' := overSiteHom hR hN tR
  obtain ⟨comp', hc₁, hc₂⟩ := exists_trans_overSiteHom hN hR sR tR comp hcomp₁ hcomp₂
  obtain ⟨X, hX, q, hqs, hqe, hqk⟩ := exists_quotient_of_witnesses B S hS sR' tR' hsE htE
    (jointlyMono₂_post_overSiteHom hN hR sR tR hjm)
    (overSiteHom hN hR refl) (by rw [overSiteHom_comp, hrefl₁, overSiteHom_id])
    (by rw [overSiteHom_comp, hrefl₂, overSiteHom_id])
    (overSiteHom hR hR symm) (by rw [overSiteHom_comp, hsymm₁])
    (by rw [overSiteHom_comp, hsymm₂]) comp' hc₁ hc₂
  have : B.topology.Subcanonical := BigFppfSite.subcanonical_topology B
  have : (BigFppfOver.topology B S hS).Subcanonical :=
    inferInstanceAs (B.topology.over (B.obj hS)).Subcanonical
  have hyV : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (yoneda.obj V) :=
    (isSheaf_iff_isSheaf_of_type _ _).mpr
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)
  obtain ⟨p, hp, -⟩ := existsUnique_desc_of_surjective_etale_atlas B S hS hX.isSheaf q hqk hqs hqe
    hyV (yoneda.map (overSiteToBase N hN)) (by
      rw [← Functor.map_comp, ← Functor.map_comp, overSiteHom_comp_overSiteToBase,
        overSiteHom_comp_overSiteToBase])
  exact ⟨X, hX, q, p, hqs, hqe, hqk, hp⟩

end OverSite

/-! ### The kernel pair of an étale atlas -/

section KernelPair

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {N R : BigFppfOver B S hS}
  {n : yoneda.obj N ⟶ F} {s t : R ⟶ N} (hR : IsPullback (yoneda.map s) (yoneda.map t) n n)

include hR in
/-- The two projections of the kernel pair of an étale atlas are étale. -/
theorem etale_kernelPair
    (hn : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf n) :
    Etale ((BigFppfOver.toScheme B S hS).map s) ∧ Etale ((BigFppfOver.toScheme B S hS).map t) := by
  have hP : MorphismProperty.IsStableUnderBaseChange (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    inferInstance
  exact ⟨(presheaf_yoneda_map_iff B S hS hP s).1 (presheaf_of_isPullback B S hS hR.flip hn),
    (presheaf_yoneda_map_iff B S hS hP t).1 (presheaf_of_isPullback B S hS hR hn)⟩

/-- A kernel pair receives a morphism lifting two maps to `N` that agree after the atlas. -/
private theorem exists_hom_of_yoneda_map_comp_eq
    (hR : IsPullback (yoneda.map s) (yoneda.map t) n n) {X : BigFppfOver B S hS} {a b : X ⟶ N}
    (hab : yoneda.map a ≫ n = yoneda.map b ≫ n) : ∃ r : X ⟶ R, r ≫ s = a ∧ r ≫ t = b := by
  refine ⟨yoneda.preimage (hR.lift _ _ hab), yoneda.map_injective ?_, yoneda.map_injective ?_⟩
  · rw [Functor.map_comp, Functor.map_preimage, hR.lift_fst]
  · rw [Functor.map_comp, Functor.map_preimage, hR.lift_snd]

include hR in
/-- **Reflexivity of a kernel pair**, with a witness. -/
theorem exists_refl_kernelPair : ∃ r : N ⟶ R, r ≫ s = 𝟙 N ∧ r ≫ t = 𝟙 N :=
  exists_hom_of_yoneda_map_comp_eq hR rfl

include hR in
/-- **Symmetry of a kernel pair**, with a witness. -/
theorem exists_symm_kernelPair : ∃ σ : R ⟶ R, σ ≫ s = t ∧ σ ≫ t = s :=
  exists_hom_of_yoneda_map_comp_eq hR hR.w.symm

include hR in
/-- **Transitivity of a kernel pair**, with a witness. -/
theorem exists_trans_kernelPair :
    ∃ τ : pullback t s ⟶ R, τ ≫ s = pullback.fst t s ≫ s ∧ τ ≫ t = pullback.snd t s ≫ t :=
  exists_hom_of_yoneda_map_comp_eq hR (by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hR.w, ← Category.assoc,
      ← Functor.map_comp, pullback.condition, Functor.map_comp, Category.assoc, hR.w])

include hR in
/-- The two projections of a kernel pair agree after the structure morphism. -/
theorem kernelPair_comp_eq {V : BigFppfOver B S hS} {p : F ⟶ yoneda.obj V} {n₀ : N ⟶ V}
    (hn₀ : yoneda.map n₀ = n ≫ p) : s ≫ n₀ = t ≫ n₀ :=
  yoneda.map_injective (by
    rw [Functor.map_comp, Functor.map_comp, hn₀, ← Category.assoc, hR.w, Category.assoc])

include hR in
/-- **The kernel pair of an étale atlas of a separated space is closed in `N ×_V N`.** -/
theorem isClosedImmersion_lift_kernelPair {V : BigFppfOver B S hS} {p : F ⟶ yoneda.obj V}
    (hsep : IsSeparated B S hS p) {n₀ : N ⟶ V} (hn₀ : yoneda.map n₀ = n ≫ p) :
    AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      (pullback.lift s t (kernelPair_comp_eq hR hn₀))) := by
  let ι := pullback.lift s t (kernelPair_comp_eq hR hn₀)
  have hY : IsPullback (yoneda.map (pullback.fst n₀ n₀)) (yoneda.map (pullback.snd n₀ n₀))
      (n ≫ p) (n ≫ p) := by
    rw [← hn₀]
    exact (IsPullback.of_hasPullback n₀ n₀).map yoneda
  let m : yoneda.obj (pullback n₀ n₀) ⟶ pullback p p :=
    pullback.lift (yoneda.map (pullback.fst n₀ n₀) ≫ n) (yoneda.map (pullback.snd n₀ n₀) ≫ n)
      (by simpa only [Category.assoc] using hY.w)
  have hsq : IsPullback (yoneda.map s ≫ n) (yoneda.map ι) (pullback.diagonal p) m := by
    refine (pullback_map_diagonal_isPullback (f := n) (g := n) (i := p)).of_iso
      hR.isoPullback.symm (Iso.refl _) hY.isoPullback.symm (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      rw [← Category.assoc, IsPullback.isoPullback_inv_fst]
    · simp only [Iso.symm_hom]
      rw [← cancel_mono hY.isoPullback.hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        Category.assoc]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.comp_id, Category.assoc, Category.assoc,
          IsPullback.isoPullback_hom_fst, ← Functor.map_comp, pullback.lift_fst,
          IsPullback.isoPullback_inv_fst]
      · rw [pullback.lift_snd, Category.comp_id, Category.assoc, Category.assoc,
          IsPullback.isoPullback_hom_snd, ← Functor.map_comp, pullback.lift_snd,
          IsPullback.isoPullback_inv_snd]
    · simp
    · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id]
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ← Category.assoc,
          IsPullback.isoPullback_inv_fst]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, ← Category.assoc,
          IsPullback.isoPullback_inv_snd]
  have hP : MorphismProperty.IsStableUnderBaseChange
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) := inferInstance
  exact (presheaf_yoneda_map_iff B S hS hP ι).1 (presheaf_of_isPullback B S hS hsq hsep)

end KernelPair

end AlgebraicGeometry.Space

end
