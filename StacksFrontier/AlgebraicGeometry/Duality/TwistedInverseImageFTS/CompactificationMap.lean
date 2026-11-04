module

public import StacksFrontier.AlgebraicGeometry.Duality.SeparatedFiniteTypeProper
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BoundedBelowPlus
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.ProperRestriction
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.RestrictionSupport
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompositionMonoidal
public import StacksFrontier.CategoryTheory.Monoidal.ComparisonMapIdentity

/-!
# The upper shriek functor on `D⁺_QCoh` and morphisms of compactifications

Let `f : X ⟶ Y` be a morphism of `AlgebraicGeometry.FTS S`. The upper shriek functor
`f^! = j^* ∘ ā` of a compactification `j` ([Stacks, Tag 0A9Y]) carries `D⁺_QCoh(𝒪_Y)` into
`D⁺_QCoh(𝒪_X)`: `ā` does by [Stacks, Tag 0A9I], and restriction to an open is exact.

For two compactifications `c₁`, `c₂` of `X` over `Y` and a morphism `g : X̄₁ ⟶ X̄₂` over `Y` with
`g⁻¹(X) = X`, the transformation `α_g : c₁^* ∘ ā₁ ⟶ c₂^* ∘ ā₂` of the proof of
[Stacks, Tag 0AA0] is `ā₁ = a_g ∘ ā₂` followed by the map of [Stacks, Tag 0A9L] for the square
`X ⊆ X̄₁` over `X ⊆ X̄₂`; it is invertible wherever that map is.

## Main definitions

* `Stacks.Duality.upperShriekPlus` — `f^! : D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`.
* `Stacks.Duality.upperShriekCompactificationMap` — the transformation `α_g`.
* `Stacks.Duality.DominatingCompactification.compactification` — the closure of `X` in
  `X̄₁ ×_Y X̄₂` as a compactification of `X` over `Y`.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0A9I](https://stacks.math.columbia.edu/tag/0A9I)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality

/-! ### Lifting transformations to `D⁺_QCoh` -/

section Lift

variable {C D : Type*} [Category C] [Category D] {P : ObjectProperty D}
  {A B : C ⥤ P.FullSubcategory}

/-- A transformation between functors into a full subcategory, invertible at every object, gives
an isomorphism of the functors. -/
def isoOfNatTransι (τ : A ⋙ P.ι ⟶ B ⋙ P.ι) [∀ K, IsIso (τ.app K)] : A ≅ B :=
  haveI := NatIso.isIso_of_isIso_app τ
  ((ObjectProperty.fullyFaithfulι P).whiskeringRight C).preimageIso (asIso τ)

/-- The component of `isoOfNatTransι τ` at `K`, as a morphism of `D`, is `τ.app K`. -/
@[simp]
theorem isoOfNatTransι_hom_app_hom (τ : A ⋙ P.ι ⟶ B ⋙ P.ι) [∀ K, IsIso (τ.app K)] (K : C) :
    ((isoOfNatTransι τ).hom.app K).hom = τ.app K :=
  rfl

end Lift

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y : FTS S} (f : X ⟶ Y)

/-! ### `f^!` preserves `D⁺_QCoh` -/

section Plus

variable (c : CompactificationOf (Over.mk f.left))

/-- **`f^!` carries `D⁺_QCoh(𝒪_Y)` into `D⁺_QCoh(𝒪_X)`.** The twisted inverse image `ā` of the
compactification preserves bounded-below objects by [Stacks, Tag 0A9I], and restriction to the
open `X` preserves each `D^{≥ n}`. -/
theorem isBoundedBelow_upperShriek_obj (K : quasiCoherentDerivedCategory Y.left)
    (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    DerivedCategoryB.IsBoundedBelow ((upperShriek f c).obj K).obj := by
  obtain ⟨n, hn⟩ := (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).1
    (isBoundedBelow_twistedInverseImage_obj c.toBase K hK)
  refine DerivedCategoryB.isBoundedBelow_of_iso
    ((ObjectProperty.ι _).mapIso
      ((restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback c.immersion).app _)) ?_
  exact (DerivedCategoryB.isBoundedBelow_iff_exists_isGE _).2
    ⟨n, @isGE_derivedRestrict_obj _ _ c.immersion _ _ n hn⟩

/-- **The upper shriek functor on `D⁺_QCoh`**, `f^! : D⁺_QCoh(𝒪_Y) ⥤ D⁺_QCoh(𝒪_X)`, the functor
of [Stacks, Tag 0A9Y] at the compactification `c`, restricted to bounded-below objects. -/
def upperShriekPlus :
    quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤
      quasiCoherentDerivedCategoryPlusOfModel X.left :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ upperShriek f c)
    (fun K => isBoundedBelow_upperShriek_obj f c K.obj K.property)

/-- The underlying object of `f^!` on `D⁺_QCoh` at `K` is `f^!` of the underlying object of `K`. -/
@[simp]
theorem upperShriekPlus_obj_obj (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    ((upperShriekPlus f c).obj K).obj = (upperShriek f c).obj K.obj :=
  rfl

/-- `f^!` on `D⁺_QCoh` followed by the inclusion is the inclusion followed by `f^!`. -/
def upperShriekPlusCompιIso :
    upperShriekPlus f c ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙ upperShriek f c :=
  Iso.refl _

variable {f} in
/-- A transformation between upper shriek functors invertible on `D⁺_QCoh` is an isomorphism of
the upper shriek functors on `D⁺_QCoh`. -/
def upperShriekPlusIsoOfNatTrans {c₁ c₂ : CompactificationOf (Over.mk f.left)}
    (τ : upperShriek f c₁ ⟶ upperShriek f c₂)
    (h : ∀ K : quasiCoherentDerivedCategory Y.left, DerivedCategoryB.IsBoundedBelow K.obj →
      IsIso (τ.app K)) :
    upperShriekPlus f c₁ ≅ upperShriekPlus f c₂ :=
  @isoOfNatTransι _ _ _ _ _ (upperShriekPlus f c₁) (upperShriekPlus f c₂)
    (Functor.whiskerLeft (ObjectProperty.ι _) τ) (fun K => h K.obj K.property)

variable {f} in
/-- A transformation `(f ≫ g)^! ⟶ f^! ∘ g^!` invertible on `D⁺_QCoh` is an isomorphism of the
functors on `D⁺_QCoh`. -/
def upperShriekPlusCompIsoOfNatTrans {Z : FTS S} {g : Y ⟶ Z}
    {c : CompactificationOf (Over.mk (f ≫ g).left)} {cg : CompactificationOf (Over.mk g.left)}
    {cf : CompactificationOf (Over.mk f.left)}
    (τ : upperShriek (f ≫ g) c ⟶ upperShriek g cg ⋙ upperShriek f cf)
    (h : ∀ K : quasiCoherentDerivedCategory Z.left, DerivedCategoryB.IsBoundedBelow K.obj →
      IsIso (τ.app K)) :
    upperShriekPlus (f ≫ g) c ≅ upperShriekPlus g cg ⋙ upperShriekPlus f cf :=
  @isoOfNatTransι _ _ _ _ _ (upperShriekPlus (f ≫ g) c)
    (upperShriekPlus g cg ⋙ upperShriekPlus f cf)
    (Functor.whiskerLeft (ObjectProperty.ι _) τ) (fun K => h K.obj K.property)

end Plus

/-! ### Identifications by uniqueness of adjoints -/

section Uniq

/-- **Derived pullback along the identity is the identity on `D_QCoh`, monoidally**: the
fully faithful `L(𝟙_Z)^*` is identified with `𝟭` through its composite with itself,
`L(𝟙_Z)^* ⋙ L(𝟙_Z)^* ≅ L(𝟙_Z ≫ 𝟙_Z)^* = L(𝟙_Z)^*`, which is a monoidal isomorphism; so the
identification is compatible with the monoidal structure of `L(𝟙_Z)^*`
(`Stacks.Duality.δ_comp_quasiCoherentDerivedPullbackIdIsoOfComp`). -/
def quasiCoherentDerivedPullbackIdIsoOfComp (Z : Scheme.{u}) :
    quasiCoherentDerivedPullback' (𝟙 Z) ≅ 𝟭 (quasiCoherentDerivedCategory Z) :=
  ((Functor.FullyFaithful.id _).ofIso
    (quasiCoherentDerivedPullbackIdIso Z (isQuasicoherent_homology_derivedPullback' _)).symm
      ).isoIdOfCompIso
    (quasiCoherentDerivedPullbackCompIso (𝟙 Z) (𝟙 Z) ≪≫
      quasiCoherentDerivedPullbackCongr (Category.id_comp _))

/-- The identification `L(𝟙_Z)^* ≅ 𝟭` is compatible with the comonoidal structure map `δ` of
`L(𝟙_Z)^*`. -/
theorem δ_comp_quasiCoherentDerivedPullbackIdIsoOfComp (Z : Scheme.{u})
    (K N : quasiCoherentDerivedCategory Z) :
    Functor.OplaxMonoidal.δ (quasiCoherentDerivedPullback' (𝟙 Z)) K N ≫
        ((quasiCoherentDerivedPullbackIdIsoOfComp Z).hom.app K ⊗ₘ
          (quasiCoherentDerivedPullbackIdIsoOfComp Z).hom.app N) =
      (quasiCoherentDerivedPullbackIdIsoOfComp Z).hom.app (K ⊗ N) :=
  have : NatTrans.IsMonoidal (quasiCoherentDerivedPullbackCompIso (𝟙 Z) (𝟙 Z) ≪≫
      quasiCoherentDerivedPullbackCongr (Category.id_comp (𝟙 Z))).hom :=
    inferInstanceAs (NatTrans.IsMonoidal ((quasiCoherentDerivedPullbackCompIso (𝟙 Z) (𝟙 Z)).hom ≫
      (quasiCoherentDerivedPullbackCongr (Category.id_comp (𝟙 Z))).hom))
  Functor.FullyFaithful.δ_comp_isoIdOfCompIso _ _ K N

/-- **The twisted inverse image of the identity is the identity**, through the monoidal
identification `Stacks.Duality.quasiCoherentDerivedPullbackIdIsoOfComp` of `L(𝟙_Z)^*` with `𝟭` and
uniqueness of right adjoints twice: `R(𝟙_Z)_* ≅ 𝟭`, then `a_{𝟙_Z} ≅ 𝟭`. -/
def twistedInverseImageIdIsoOfComp (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z] :
    twistedInverseImage (𝟙 Z) (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≅
      𝟭 (quasiCoherentDerivedCategory Z) :=
  Adjunction.rightAdjointUniq
    ((twistedInverseImageAdjunction (𝟙 Z)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).ofNatIsoLeft
      (Adjunction.rightAdjointUniq
        ((quasiCoherentDerivedAdjunction (𝟙 Z) (isQuasicoherent_homology_derivedPullback' _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).ofNatIsoLeft
          (quasiCoherentDerivedPullbackIdIsoOfComp Z)) Adjunction.id)) Adjunction.id

end Uniq

/-! ### The transformation attached to a morphism of compactifications -/

section CompactificationMap

variable (c₁ c₂ : CompactificationOf (Over.mk f.left)) (g : c₁.space ⟶ c₂.space)
  (hg : g ≫ c₂.toBase = c₁.toBase) (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)

/-- The map of [Stacks, Tag 0A9L] for the square `X ⊆ X̄₁` over `X ⊆ X̄₂`. -/
abbrev compactificationRestrictionMap :=
  twistedInverseImageRestrictionMapOfIsPullback g c₂.immersion c₁.immersion sq

/-- `c₁^* ∘ ā₁ ≅ c₁^* ∘ a_g ∘ ā₂`, from `ā₁ = a_{g ≫ f̄₂} ≅ a_g ∘ ā₂`, with `c₁^*` read as
restriction through the comparison of the two left adjoints of `Rc₁_*`. -/
def upperShriekCompactificationMapSrcIso : upperShriek f c₁ ≅
    twistedInverseImage c₂.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
      twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        OpenImmersion.restrictedDerivedRestrict c₁.immersion :=
  Functor.isoWhiskerRight (twistedInverseImageCongr hg.symm _
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≪≫
      twistedInverseImageCompIso g c₂.toBase _ _ _) _ ≪≫
    Functor.isoWhiskerLeft _ (restrictedDerivedRestrictAdjointIso c₁.immersion).symm ≪≫
      Functor.associator _ _ _

/-- `c₂^* ∘ a_{𝟙_X} ∘ ... ≅ c₂^* ∘ ā₂`: the twisted inverse image of the identity is the identity
(`Stacks.Duality.twistedInverseImageIdIsoOfComp`), and restriction is `Lc₂^*` through the
comparison of the two left adjoints of `Rc₂_*`. -/
def upperShriekCompactificationMapTgtIso :
    twistedInverseImage c₂.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        OpenImmersion.restrictedDerivedRestrict c₂.immersion ⋙
          twistedInverseImage (𝟙 X.left) (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ≅
      upperShriek f c₂ :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (twistedInverseImageIdIsoOfComp X.left) ≪≫
    Functor.rightUnitor _ ≪≫ restrictedDerivedRestrictAdjointIso c₂.immersion)

/-- **The transformation `α_g : c₁^* ∘ ā₁ ⟶ c₂^* ∘ ā₂`** of the proof of [Stacks, Tag 0AA0], for
a morphism `g : X̄₁ ⟶ X̄₂` of compactifications over `Y` with `g⁻¹(X) = X`: `ā₁ = a_{g ≫ f̄₂}` is
`a_g ∘ ā₂`, and the map of [Stacks, Tag 0A9L] for the square `X ⊆ X̄₁` over `X ⊆ X̄₂` compares
`c₁^* ∘ a_g` with `c₂^*`. -/
def upperShriekCompactificationMap : upperShriek f c₁ ⟶ upperShriek f c₂ :=
  (upperShriekCompactificationMapSrcIso f c₁ c₂ g hg).hom ≫
    Functor.whiskerLeft _ (compactificationRestrictionMap f c₁ c₂ g sq) ≫
    (upperShriekCompactificationMapTgtIso f c₂).hom

/-- The component of `α_g` at `K` is the composite of the components at `K` of its three
factors. -/
theorem upperShriekCompactificationMap_app (K : quasiCoherentDerivedCategory Y.left) :
    (upperShriekCompactificationMap f c₁ c₂ g hg sq).app K =
      (upperShriekCompactificationMapSrcIso f c₁ c₂ g hg).hom.app K ≫
        (compactificationRestrictionMap f c₁ c₂ g sq).app ((twistedInverseImage c₂.toBase
          (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)).obj K) ≫
        (upperShriekCompactificationMapTgtIso f c₂).hom.app K :=
  rfl

/-- `α_g` is invertible at `K` wherever the map of [Stacks, Tag 0A9L] for `X ⊆ X̄₁` over
`X ⊆ X̄₂` is invertible at `ā₂(K)`. -/
instance isIso_upperShriekCompactificationMap_app (K : quasiCoherentDerivedCategory Y.left)
    [hK : IsIso ((compactificationRestrictionMap f c₁ c₂ g sq).app ((twistedInverseImage c₂.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs c₂.toBase)).obj K))] :
    IsIso ((upperShriekCompactificationMap f c₁ c₂ g hg sq).app K) := by
  rw [upperShriekCompactificationMap_app]
  infer_instance

end CompactificationMap

/-! ### The dominating compactification as a compactification -/

namespace DominatingCompactification

variable (j₁ j₂ : CompactificationOf (Over.mk f.left))

/-- The closure of `X` in `X̄₁ ×_Y X̄₂`, with the open immersion of `X` and the proper morphism
`Z ⟶ X̄₁ ⟶ Y`, as a compactification of `X` over `Y`. -/
def compactification : CompactificationOf (Over.mk f.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (fst f j₁ j₂ ≫ j₁.toBase))
      (Over.homMk (immersion f j₁ j₂) (by
        simp only [Over.mk_left, Over.mk_hom, Functor.id_obj]
        rw [← Category.assoc, GraphClosure.toImage_closureFst, immersion_comp_toBase f j₁])),
    ⟨(inferInstance : IsOpenImmersion (immersion f j₁ j₂)),
      (inferInstance : IsProper (fst f j₁ j₂ ≫ j₁.toBase))⟩⟩

/-- The ambient scheme of the dominating compactification is the closure of `X` in
`X̄₁ ×_Y X̄₂`. -/
@[simp]
theorem compactification_space : (compactification f j₁ j₂).space = space f j₁ j₂ :=
  rfl

/-- The open immersion of the dominating compactification is that of `X` into the closure. -/
@[simp]
theorem compactification_immersion :
    (compactification f j₁ j₂).immersion = immersion f j₁ j₂ :=
  rfl

/-- The structure morphism of the dominating compactification is `Z ⟶ X̄₁ ⟶ Y`. -/
@[simp]
theorem compactification_toBase :
    (compactification f j₁ j₂).toBase = fst f j₁ j₂ ≫ j₁.toBase :=
  rfl

/-- `α` for the first projection of the dominating compactification. -/
abbrev mapFst : upperShriek f (compactification f j₁ j₂) ⟶ upperShriek f j₁ :=
  upperShriekCompactificationMap f (compactification f j₁ j₂) j₁ (fst f j₁ j₂) rfl
    (isPullback_fst f j₁ j₂)

/-- `α` for the second projection of the dominating compactification. -/
abbrev mapSnd : upperShriek f (compactification f j₁ j₂) ⟶ upperShriek f j₂ :=
  upperShriekCompactificationMap f (compactification f j₁ j₂) j₂ (snd f j₁ j₂)
    (fst_comp_toBase f j₁ j₂).symm (isPullback_snd f j₁ j₂)

end DominatingCompactification

/-! ### The isomorphisms over a Noetherian base -/

section Noetherian

variable [IsNoetherian S]

/-- The ambient scheme of a compactification over an object of `FTS S` is Noetherian when `S` is,
being proper over a Noetherian scheme. -/
instance isNoetherian_space {T : FTS S} {W : Over T.left} (c : CompactificationOf W) :
    IsNoetherian c.space :=
  isNoetherian_of_isProper c.toBase

/-- **[Stacks, Tag 0A9P] for a morphism of compactifications**: for `g : X̄₁ ⟶ X̄₂` proper with
`g⁻¹(X) = X`, the map of [Stacks, Tag 0A9L] for `X ⊆ X̄₁` over `X ⊆ X̄₂` is invertible on
`D⁺_QCoh(𝒪_{X̄₂})`. -/
theorem isIso_compactificationRestrictionMap_app (c₁ c₂ : CompactificationOf (Over.mk f.left))
    (g : c₁.space ⟶ c₂.space) [IsProper g]
    (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion)
    (K : quasiCoherentDerivedCategory c₂.space) (hK : DerivedCategoryB.IsBoundedBelow K.obj) :
    IsIso ((compactificationRestrictionMap f c₁ c₂ g sq).app K) :=
  isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ g _ sq K hK

/-- **The isomorphism `α_g : f^!_{c₁} ≅ f^!_{c₂}` on `D⁺_QCoh`** of the proof of
[Stacks, Tag 0AA0], for a proper morphism `g : X̄₁ ⟶ X̄₂` of compactifications over `Y` with
`g⁻¹(X) = X`. -/
def upperShriekCompactificationIso (c₁ c₂ : CompactificationOf (Over.mk f.left))
    (g : c₁.space ⟶ c₂.space) [IsProper g] (hg : g ≫ c₂.toBase = c₁.toBase)
    (sq : IsPullback c₁.immersion (𝟙 X.left) g c₂.immersion) :
    upperShriekPlus f c₁ ≅ upperShriekPlus f c₂ :=
  upperShriekPlusIsoOfNatTrans (upperShriekCompactificationMap f c₁ c₂ g hg sq) fun K hK =>
    isIso_upperShriekCompactificationMap_app f c₁ c₂ g hg sq K
      (hK := isIso_compactificationRestrictionMap_app f c₁ c₂ g sq _
        (isBoundedBelow_twistedInverseImage_obj c₂.toBase K hK))

open DominatingCompactification in
/-- **Two compactifications give isomorphic upper shriek functors on `D⁺_QCoh`**, through the
dominating compactification: `f^!_{j₁} ≅ f^!_Z ≅ f^!_{j₂}`. This is the content of
[Stacks, Tag 0AA0]. -/
def DominatingCompactification.upperShriekPlusIso (j₁ j₂ : CompactificationOf (Over.mk f.left)) :
    upperShriekPlus f j₁ ≅ upperShriekPlus f j₂ :=
  haveI : IsProper (X := (compactification f j₁ j₂).space) (fst f j₁ j₂) :=
    (inferInstance : IsProper (fst f j₁ j₂))
  haveI : IsProper (X := (compactification f j₁ j₂).space) (snd f j₁ j₂) :=
    (inferInstance : IsProper (snd f j₁ j₂))
  (upperShriekCompactificationIso f (compactification f j₁ j₂) j₁ (fst f j₁ j₂) rfl
      (isPullback_fst f j₁ j₂)).symm ≪≫
    upperShriekCompactificationIso f (compactification f j₁ j₂) j₂ (snd f j₁ j₂)
      (fst_comp_toBase f j₁ j₂).symm (isPullback_snd f j₁ j₂)

/-- **The composition isomorphism `(f ≫ g)^! ≅ f^! ∘ g^!` on `D⁺_QCoh`**, for arbitrary
compactifications `cf`, `cg`, `cfg` of `f`, `g` and `f ≫ g`. It is computed through the
compactification `P` of `X` over `Z` proper over `Ȳ` and its inverse image `Q` over `Y`
(`Stacks.Duality.CompCompactification`): `a_{P/Z} ≅ a_{P/Ȳ} ∘ a_{Ȳ/Z}` restricted to `X`, the map
of [Stacks, Tag 0A9L] for `Q ⊆ P` over `Y ⊆ Ȳ`, and the comparisons of `cfg` with `P` and of `Q`
with `cf`; [Stacks, Tag 0A9P] makes all of them invertible on `D⁺_QCoh`. This is the content of
[Stacks, Tag 0ATX] together with [Stacks, Tag 0AA0]. -/
def upperShriekCompIso {Z : FTS S} (g : Y ⟶ Z) (cf : CompactificationOf (Over.mk f.left))
    (cg : CompactificationOf (Over.mk g.left)) (cfg : CompactificationOf (Over.mk (f ≫ g).left)) :
    upperShriekPlus (f ≫ g) cfg ≅ upperShriekPlus g cg ⋙ upperShriekPlus f cf :=
  DominatingCompactification.upperShriekPlusIso (f ≫ g) cfg
      (CompCompactification.compactification f g cg cfg) ≪≫
    upperShriekPlusCompIsoOfNatTrans (CompCompactification.upperShriekCompHom f g cg cfg)
      (fun K hK => CompCompactification.isIso_upperShriekCompHom_app f g cg cfg K
        (hK := isIso_twistedInverseImageRestrictionMap_app_of_isProper _ _ _ _ _ _
          (isBoundedBelow_twistedInverseImage_obj cg.toBase K hK))) ≪≫
    Functor.isoWhiskerLeft (upperShriekPlus g cg)
      (DominatingCompactification.upperShriekPlusIso f
        (CompCompactification.restrictCompactification f g cg cfg) cf)

variable {f} in
/-- Equal morphisms have isomorphic upper shriek functors on `D⁺_QCoh`, at any
compactifications. -/
def upperShriekPlusCongr {f' : X ⟶ Y} (h : f = f') (c : CompactificationOf (Over.mk f.left))
    (c' : CompactificationOf (Over.mk f'.left)) : upperShriekPlus f c ≅ upperShriekPlus f' c' := by
  subst h
  exact DominatingCompactification.upperShriekPlusIso f c c'

end Noetherian

end Stacks.Duality

end
