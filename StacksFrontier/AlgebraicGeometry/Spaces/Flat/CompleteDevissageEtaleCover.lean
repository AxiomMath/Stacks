module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeRestrictionEtalePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.ExistenceCompleteDevissage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Complete dévissages of a finite type module on an algebraic space

Let `X ⟶ Y` be a finite type morphism of algebraic spaces over a scheme `S`, let `F` be a finite
type quasi-coherent `𝒪_X`-module and let `y` be a point of `Y`. Stacks 0CWJ asserts that there
are an étale morphism `(Y', y') ⟶ (Y, y)` with `Y'` an affine scheme and étale morphisms
`hᵢ : Wᵢ ⟶ X_{Y'}`, `i = 1, …, n`, such that the pullback `Fᵢ` of `F` to each `Wᵢ` has a complete
dévissage `Fᵢ/Wᵢ/Y'` over `y'`, and such that `|(X_{Y'})_{y'}| ⊆ ⋃ hᵢ(Wᵢ)`.

This file proves that statement,
`AlgebraicGeometry.Space.exists_affine_etale_completeDevissage_cover`, from the source's
hypotheses and no others, along the source's proof: the question is étale local
on `Y`, so `Y` may be replaced by an affine étale chart `Y₁` through `y`; then `X ×_Y Y₁` is
quasi-compact and has an affine surjective étale cover `X'` (Stacks 03H6); and Stacks 05HU for
the morphism of affine schemes `X' ⟶ Y₁` and the restriction of `F` to `X'` gives the conclusion.

## Main results

* `AlgebraicGeometry.exists_isAffine_etaleNeighborhood_completeDevissage_affineCover`: Stacks 05HU
  with an affine elementary étale neighbourhood *and* affine sources of the covering étale
  morphisms.
* `AlgebraicGeometry.CompleteDevissage.ofModuleIso`: a complete dévissage of a module is one of
  any isomorphic module.
* `AlgebraicGeometry.Space.exists_siteObjects_completeDevissage_cover`: the output of the previous
  result over a fibre product `U₀ ×_{Y₁} Y'` of objects of the site, realized by objects of the
  site.
* `AlgebraicGeometry.Space.exists_affine_etale_completeDevissage_cover`: **Stacks 0CWJ.**

## Implementation notes

**Objects of the site.** The objects of the big fppf site of `S` are the schemes below a size
cutoff, while Stacks 05HU produces schemes with no size bound. The schemes it produces here are,
however, affine and of finite type over objects of the site: the elementary étale neighbourhood
`Y'` of the point of `Y₁` is affine and étale over `Y₁`, and the sources of the covering étale
morphisms can be taken affine and are étale over `X' ×_{Y₁} Y'`, hence of finite type over `X'`.
By Stacks 04T7 (`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`) their size is bounded by
that of `Y₁`, respectively `X'`, so they are objects of the site, and the covering morphisms are
morphisms of algebraic spaces into `X_{Y'}`. The sources can be taken affine because the source of
a nonempty complete dévissage is affine, while a source carrying the empty dévissage of the zero
module may be replaced by any of its affine opens; quasi-compactness of the fibre keeps the family
finite.

**The statement.** Étaleness of `Y' ⟶ Y` and of `hᵢ` is `AlgebraicGeometry.Space.IsEtale`
(Stacks 03FR). The pullback `Fᵢ` of `F` to `Wᵢ` is the restriction
`AlgebraicGeometry.Space.restrictToChart` of `F` to the étale chart `Wᵢ ⟶ X_{Y'} ⟶ X`, which is
an étale chart of `X` (that it is one is part of the conclusion). The morphism `Wᵢ ⟶ Y'` along
which the dévissage is taken is the morphism of the site `aᵢ` with `hᵢ ≫ pr₁ = aᵢ`, and the point
`y'` enters through the point of the scheme `Y'` it determines. The covering condition is stated on
points of the algebraic space `X_{Y'}`: every point lying over `y'` is in the image of some `hᵢ`.

## References

* [Stacks Project, Tag 0CWJ](https://stacks.math.columbia.edu/tag/0CWJ)
* [Stacks Project, Tag 05HU](https://stacks.math.columbia.edu/tag/05HU)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
* [Stacks Project, Tag 04T7](https://stacks.math.columbia.edu/tag/04T7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 05HU**, with an affine elementary étale neighbourhood `(S', s')` and affine sources
`Yᵢ` of the covering étale morphisms `hᵢ : Yᵢ ⟶ X ×_S S'`.

The source of a nonempty complete dévissage is affine. A source carrying the empty dévissage,
of the zero module, is replaced by its affine opens, and quasi-compactness of the fibre keeps the
family finite. -/
theorem exists_isAffine_etaleNeighborhood_completeDevissage_affineCover {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [QuasiCompact f] (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (s : S) :
    ∃ (S' : EtaleNeighborhood S s) (_ : S'.IsElementary) (_ : IsAffine S'.scheme) (n : ℕ)
      (Y : Fin n → Scheme.{u}) (_ : ∀ i, IsAffine (Y i))
      (h : ∀ i, Y i ⟶ pullback f S'.toBase) (_ : ∀ i, Etale (h i))
      (hl : ∀ i, LocallyOfFiniteType (h i ≫ pullback.snd f S'.toBase))
      (hq : ∀ i, ((Scheme.Modules.pullback
        (h i ≫ pullback.fst f S'.toBase)).obj F).IsQuasicoherent)
      (ht : ∀ i, ((Scheme.Modules.pullback
        (h i ≫ pullback.fst f S'.toBase)).obj F).IsFiniteType),
      (∀ i, Nonempty (@CompleteDevissage _ _ (h i ≫ pullback.snd f S'.toBase)
        ((Scheme.Modules.pullback (h i ≫ pullback.fst f S'.toBase)).obj F) S'.point
        (hl i) (hq i) (ht i))) ∧
        pullback.snd f S'.toBase ⁻¹' {S'.point} ⊆ ⋃ i, Set.range (h i) := by
  classical
  obtain ⟨S', hS', hS'aff, n, Y, h, het, hl, hq, ht, hD, hcov⟩ :=
    exists_isAffine_etaleNeighborhood_completeDevissage_cover f F s
  -- Every point of the fibre lies in the image of an affine scheme étale over `X ×_S S'`
  -- carrying a complete dévissage.
  have key : ∀ z : {z : ↥(pullback f S'.toBase) // pullback.snd f S'.toBase z = S'.point},
      ∃ (A : Scheme.{u}) (e : A ⟶ pullback f S'.toBase),
        IsAffine A ∧ Etale e ∧ z.1 ∈ Set.range e ∧
        ∃ (hl : LocallyOfFiniteType (e ≫ pullback.snd f S'.toBase))
          (hq : ((Scheme.Modules.pullback (e ≫ pullback.fst f S'.toBase)).obj F).IsQuasicoherent)
          (ht : ((Scheme.Modules.pullback (e ≫ pullback.fst f S'.toBase)).obj F).IsFiniteType),
          Nonempty (@CompleteDevissage _ _ (e ≫ pullback.snd f S'.toBase)
            ((Scheme.Modules.pullback (e ≫ pullback.fst f S'.toBase)).obj F) S'.point
            hl hq ht) := by
    rintro ⟨z, hz⟩
    obtain ⟨i, w, rfl⟩ := Set.mem_iUnion.mp (hcov (by simpa using hz))
    obtain ⟨D⟩ := hD i
    match D with
    | .nonempty data =>
      exact ⟨Y i, h i, isAffine_source_of_devissageChain data.chain, het i, ⟨w, rfl⟩,
        hl i, hq i, ht i, hD i⟩
    | .empty hzero =>
      obtain ⟨_, ⟨(V : (Y i).Opens), hV : IsAffine _, rfl⟩, hwV, -⟩ :=
        (Y i).isBasis_affineOpens.exists_subset_of_mem_open (a := w) (by trivial) isOpen_univ
      have := het i
      have := hl i
      have hl' : LocallyOfFiniteType ((V.ι ≫ h i) ≫ pullback.snd f S'.toBase) := by
        rw [Category.assoc]
        infer_instance
      have hq' : ((Scheme.Modules.pullback
          ((V.ι ≫ h i) ≫ pullback.fst f S'.toBase)).obj F).IsQuasicoherent :=
        Stacks.Modules.isQuasicoherent_pullback _ F inferInstance
      have ht' : ((Scheme.Modules.pullback
          ((V.ι ≫ h i) ≫ pullback.fst f S'.toBase)).obj F).IsFiniteType :=
        SheafOfModules.pullback_isFiniteType _ F
      refine ⟨V, V.ι ≫ h i, hV, inferInstance, ⟨⟨w, hwV⟩, rfl⟩, hl', hq', ht', ⟨.empty ?_⟩⟩
      exact ((Scheme.Modules.pullback V.ι).map_isZero hzero).of_iso
        ((Scheme.Modules.pullbackCongr (Category.assoc _ _ _)).app F ≪≫
          ((Scheme.Modules.pullbackComp V.ι (h i ≫ pullback.fst f S'.toBase)).app F).symm)
  choose A e hA he hmem hl' hq' ht' hD' using key
  -- The fibre is quasi-compact and the images of the étale morphisms are open.
  obtain ⟨t, htcov⟩ := (Scheme.Hom.isCompact_preimage_singleton
      (pullback.snd f S'.toBase) S'.point).elim_finite_subcover
    (fun z => Set.range (e z)) (fun z => by have := he z; exact (e z).isOpenMap.isOpen_range)
    (fun z hz => Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hmem ⟨z, hz⟩⟩)
  refine ⟨S', hS', hS'aff, t.card, fun i => A (t.equivFin.symm i),
    fun i => hA _, fun i => e _, fun i => he _, fun i => hl' _, fun i => hq' _,
    fun i => ht' _, fun i => hD' _, fun z hz => ?_⟩
  obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp (htcov hz)
  refine Set.mem_iUnion.mpr ⟨t.equivFin ⟨x, hx⟩, ?_⟩
  exact (congrArg (fun j => z ∈ Set.range (e j))
    (congrArg Subtype.val (t.equivFin.symm_apply_apply ⟨x, hx⟩))).mpr hzx

/-- A complete dévissage of `F/X/S` over `s`, empty or not, is one of any isomorphic module. -/
def CompleteDevissage.ofModuleIso {X S : Scheme.{u}} {f : X ⟶ S} {F F' : X.Modules} {s : S}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] [F'.IsQuasicoherent]
    [F'.IsFiniteType] (D : CompleteDevissage f F s) (e : F' ≅ F) : CompleteDevissage f F' s :=
  match D with
  | .empty hzero => .empty (hzero.of_iso e)
  | .nonempty data => .nonempty (data.ofModuleIso e)

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_CompleteDevissageEtaleCover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_CompleteDevissageEtaleCover
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_CompleteDevissageEtaleCover B S hS).has_limit _

section SiteObjects

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

local notation "𝒯" => BigFppfOver.toScheme B S hS

/-- The output of Stacks 05HU, with affine sources, over a fibre product `U₀ ×_{Y₁} Y'` of
objects of the site, realized by objects of the site.

Let `ĝ : U₀ ⟶ Y₁` and `ι' : Y' ⟶ Y₁` be morphisms of the big fppf site of `S`, the second étale,
let `G` be a module on the scheme `U₀` and let `t'` be a point of the scheme `Y'`. Given affine
schemes `Aᵢ` with étale morphisms `eᵢ` to the fibre product of schemes `U₀ ×_{Y₁} Y'`, whose
images cover the fibre over `t'` and each of which carries a complete dévissage of the pullback
of `G` over `t'`, there are objects `Wᵢ` of the site with morphisms `kᵢ` to the fibre product
`U₀ ×_{Y₁} Y'` in the site, étale as morphisms of schemes, whose images still cover the fibre
over `t'` and such that the pullback of `G` along `kᵢ ≫ pr₁` has a complete dévissage along
`kᵢ ≫ pr₂` over `t'`.

Each `Aᵢ` is affine and of finite type over `U₀`, so by Stacks 04T7 it is an object of the site,
and `Wᵢ` is `Aᵢ` regarded as such. -/
theorem exists_siteObjects_completeDevissage_cover {U₀ Y₁ Y' : BigFppfOver B S hS}
    (ĝ : U₀ ⟶ Y₁) (ι' : Y' ⟶ Y₁) [Etale ((𝒯).map ι')] (G : ((𝒯).obj U₀).Modules) (t' : (𝒯).obj Y')
    {n : ℕ} (A : Fin n → Scheme.{u}) (hA : ∀ i, IsAffine (A i))
    (e : ∀ i, A i ⟶ pullback ((𝒯).map ĝ) ((𝒯).map ι')) (he : ∀ i, Etale (e i))
    (hl : ∀ i, LocallyOfFiniteType (e i ≫ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι')))
    (hq : ∀ i, ((Scheme.Modules.pullback
      (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι'))).obj G).IsQuasicoherent)
    (ht : ∀ i, ((Scheme.Modules.pullback
      (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι'))).obj G).IsFiniteType)
    (hD : ∀ i, Nonempty (@CompleteDevissage _ _ (e i ≫ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι'))
      ((Scheme.Modules.pullback (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι'))).obj G) t'
      (hl i) (hq i) (ht i)))
    (hcov : pullback.snd ((𝒯).map ĝ) ((𝒯).map ι') ⁻¹' {t'} ⊆ ⋃ i, Set.range (e i)) :
    ∃ (W : Fin n → BigFppfOver B S hS) (b : ∀ i, W i ⟶ U₀) (a : ∀ i, W i ⟶ Y')
      (k : ∀ i, W i ⟶ pullback ĝ ι'),
      (∀ i, k i ≫ pullback.fst ĝ ι' = b i) ∧ (∀ i, k i ≫ pullback.snd ĝ ι' = a i) ∧
      (∀ i, Etale ((𝒯).map (k i))) ∧ (∀ i, Etale ((𝒯).map (b i))) ∧
      ∃ (hl : ∀ i, LocallyOfFiniteType ((𝒯).map (a i)))
        (hq : ∀ i, ((Scheme.Modules.pullback ((𝒯).map (b i))).obj G).IsQuasicoherent)
        (ht : ∀ i, ((Scheme.Modules.pullback ((𝒯).map (b i))).obj G).IsFiniteType),
        (∀ i, Nonempty (@CompleteDevissage _ _ ((𝒯).map (a i))
          ((Scheme.Modules.pullback ((𝒯).map (b i))).obj G) t' (hl i) (hq i) (ht i))) ∧
        ∀ z : (𝒯).obj (pullback ĝ ι'), (𝒯).map (pullback.snd ĝ ι') z = t' →
          ∃ (i : Fin n) (w : (𝒯).obj (W i)), (𝒯).map (k i) w = z := by
  -- Each affine source is an object of the site: it is of finite type over `U₀`.
  have hAc : ∀ i, B.Contains (A i) := fun i => by
    have := hA i
    have := he i
    exact (Scheme.size_le_of_locallyOfFiniteType
      (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι'))).trans_lt U₀.left.property
  have hw : ∀ {P Q : BigFppfOver B S hS} (g : P ⟶ Q),
      (𝒯).map g ≫ B.inclusion.map Q.hom = B.inclusion.map P.hom := fun g => by
    show B.inclusion.map g.left ≫ _ = _
    rw [← Functor.map_comp]
    exact congrArg _ (Over.w g)
  have hw' : ∀ i, (e i ≫ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι')) ≫ B.inclusion.map Y'.hom =
      (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι')) ≫ B.inclusion.map U₀.hom := fun i => by
    rw [← hw ĝ, ← hw ι', Category.assoc, Category.assoc, ← Category.assoc (pullback.snd _ _),
      ← pullback.condition, Category.assoc]
  -- The sources as objects of the site, with their two projections and the induced morphism to
  -- the fibre product of the site.
  let W : Fin n → BigFppfOver B S hS := fun i => siteObject B S hS (hAc i)
    ((e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι')) ≫ B.inclusion.map U₀.hom)
  let b : ∀ i, W i ⟶ U₀ := fun i => Over.homMk
    (ObjectProperty.homMk (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι'))) rfl
  let a : ∀ i, W i ⟶ Y' := fun i => Over.homMk
    (ObjectProperty.homMk (e i ≫ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι')))
    (by ext1; exact hw' i)
  have hk : ∀ i, b i ≫ ĝ = a i ≫ ι' := fun i => by
    refine (𝒯).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    show (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι')) ≫ (𝒯).map ĝ =
      (e i ≫ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι')) ≫ (𝒯).map ι'
    rw [Category.assoc, Category.assoc, pullback.condition]
  let k : ∀ i, W i ⟶ pullback ĝ ι' := fun i => pullback.lift (b i) (a i) (hk i)
  -- The underlying scheme of the fibre product of the site is the fibre product of schemes.
  let isoP : (𝒯).obj (pullback ĝ ι') ≅ pullback ((𝒯).map ĝ) ((𝒯).map ι') :=
    PreservesPullback.iso 𝒯 ĝ ι'
  have hisofst : isoP.hom ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι') = (𝒯).map (pullback.fst ĝ ι') :=
    PreservesPullback.iso_hom_fst _ _ _
  have hisosnd : isoP.hom ≫ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι') = (𝒯).map (pullback.snd ĝ ι') :=
    PreservesPullback.iso_hom_snd _ _ _
  have hkT : ∀ i, (𝒯).map (k i) = e i ≫ isoP.inv := fun i => by
    rw [Iso.eq_comp_inv]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hisofst, ← Functor.map_comp, pullback.lift_fst]
      rfl
    · rw [Category.assoc, hisosnd, ← Functor.map_comp, pullback.lift_snd]
      rfl
  refine ⟨W, b, a, k, fun i => pullback.lift_fst _ _ _, fun i => pullback.lift_snd _ _ _,
    fun i => ?_, fun i => ?_, hl, hq, ht, hD, fun z hz => ?_⟩
  · have := he i
    rw [hkT]
    infer_instance
  · have := he i
    show Etale (e i ≫ pullback.fst ((𝒯).map ĝ) ((𝒯).map ι'))
    infer_instance
  · have hzz : isoP.hom z ∈ pullback.snd ((𝒯).map ĝ) ((𝒯).map ι') ⁻¹' {t'} := by
      rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, hisosnd, hz]
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.mp (hcov hzz)
    refine ⟨i, w, ?_⟩
    rw [hkT, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl

/-- Let `c : X' ⟶ X ×_Y Y₁` with `ĝ : X' ⟶ Y₁` its first component and let `ι' : Y' ⟶ Y₁`.
The morphism `X' ×_{Y₁} Y' ⟶ X ×_Y Y'` induced by `ĝ` and `ι'` is the base change of `c` along
`X ×_Y Y' ⟶ X ×_Y Y₁`. -/
private theorem isPullback_yoneda_pullback_baseChange {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) {X' Y₁ Y' : BigFppfOver B S hS} (q₁ : yoneda.obj Y₁ ⟶ Y)
    (c : yoneda.obj X' ⟶ pullback q₁ f) (ĝ : X' ⟶ Y₁) (hĝ : yoneda.map ĝ = c ≫ pullback.fst q₁ f)
    (ι' : Y' ⟶ Y₁) (φ : yoneda.obj (pullback ĝ ι') ⟶ pullback (yoneda.map ι' ≫ q₁) f)
    (hφfst : φ ≫ pullback.fst _ f = yoneda.map (pullback.snd ĝ ι'))
    (hφsnd : φ ≫ pullback.snd _ f = yoneda.map (pullback.fst ĝ ι') ≫ c ≫ pullback.snd q₁ f)
    (ψ : pullback (yoneda.map ι' ≫ q₁) f ⟶ pullback q₁ f)
    (hψfst : ψ ≫ pullback.fst q₁ f = pullback.fst _ f ≫ yoneda.map ι')
    (hψsnd : ψ ≫ pullback.snd q₁ f = pullback.snd _ f) :
    IsPullback (yoneda.map (pullback.fst ĝ ι')) φ c ψ := by
  have hright : IsPullback ψ (pullback.fst _ f) (pullback.fst q₁ f) (yoneda.map ι') := by
    refine IsPullback.of_right (h₁₂ := pullback.snd q₁ f) (h₂₂ := q₁) (v₁₃ := f) ?_ hψfst
      (IsPullback.of_hasPullback q₁ f).flip
    rw [hψsnd]
    exact (IsPullback.of_hasPullback _ f).flip
  refine IsPullback.of_bot (v₂₁ := pullback.fst _ f) (v₂₂ := pullback.fst q₁ f) ?_ ?_ hright
  · rw [hφfst, ← hĝ]
    exact (IsPullback.of_hasPullback ĝ ι').map yoneda
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ← hĝ, hψfst, ← Category.assoc, hφfst,
        ← yoneda.map_comp, ← yoneda.map_comp, pullback.condition]
    · rw [Category.assoc, Category.assoc, hψsnd, hφsnd]

end SiteObjects

/-- **Stacks Project, Tag 0CWJ.** Let `X ⟶ Y` be a finite type morphism of algebraic spaces over
`S`, let `F` be a finite type quasi-coherent `𝒪_X`-module and let `y` be a point of `Y`. There
are an étale morphism `q : (Y', y') ⟶ (Y, y)` with `Y'` an affine scheme, and étale morphisms
`hᵢ : Wᵢ ⟶ X_{Y'} = Y' ×_Y X`, `i = 1, …, n`, from schemes `Wᵢ`, such that for each `i` the
pullback `Fᵢ` of `F` to `Wᵢ` (its restriction to the étale chart `Wᵢ ⟶ X_{Y'} ⟶ X`) has a
complete dévissage `Fᵢ/Wᵢ/Y'` over `y'`, the morphism `Wᵢ ⟶ Y'` being the `aᵢ` with
`hᵢ ≫ pr₁ = aᵢ`, and such that every point of `X_{Y'}` lying over `y'` is in the image of some
`hᵢ`, that is, `|(X_{Y'})_{y'}| ⊆ ⋃ hᵢ(Wᵢ)`. -/
@[stacks 0CWJ "the full statement, proved from the source's hypotheses; nothing is assumed"]
theorem exists_affine_etale_completeDevissage_cover (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : IsFiniteType B S hS f) (F : Modules.{u, u} B S hS X hX)
    (hFq : F.IsQuasicoherentOnSite) (hFt : SheafOfModules.IsFiniteTypeOnSite F)
    (y : points B S hS Y) :
    ∃ (Y' : BigFppfOver B S hS) (q : yoneda.obj Y' ⟶ Y) (y' : points B S hS (yoneda.obj Y')),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Y') ∧ IsEtale B S hS q ∧
      pointsMap B S hS (yoneda.obj Y') q y' = y ∧
      ∃ (n : ℕ) (W : Fin n → BigFppfOver B S hS)
        (h : ∀ i, yoneda.obj (W i) ⟶ pullback q f) (_ : ∀ i, IsEtale B S hS (h i))
        (hW : ∀ i, IsEtaleChart B S hS X (CostructuredArrow.mk (h i ≫ pullback.snd q f)))
        (a : ∀ i, W i ⟶ Y') (_ : ∀ i, h i ≫ pullback.fst q f = yoneda.map (a i))
        (hl : ∀ i, LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map (a i)))
        (hq : ∀ i, (restrictToChart B S hS hX F ⟨_, hW i⟩).IsQuasicoherent)
        (ht : ∀ i, (restrictToChart B S hS hX F ⟨_, hW i⟩).IsFiniteType),
        (∀ i, Nonempty (@CompleteDevissage _ _ ((BigFppfOver.toScheme B S hS).map (a i))
          (restrictToChart B S hS hX F ⟨_, hW i⟩) (pointsToScheme B S hS Y' y')
          (hl i) (hq i) (ht i))) ∧
        ∀ x : points B S hS (pullback q f),
          pointsMap B S hS _ (pullback.fst q f) x = y' →
            ∃ (i : Fin n) (z : points B S hS (yoneda.obj (W i))),
              pointsMap B S hS _ (h i) z = x := by
  classical
  -- Reduction to an affine base: an affine étale chart `Y₁ ⟶ Y` through `y`.
  have hc := exists_affine_etale_chart_at_point B S hS Y hY y
  obtain ⟨Y₁, q₁, hY₁aff, hq₁et, w, hw⟩ := hc
  have hY₁alg : IsAlgebraicSpace B S hS (yoneda.obj Y₁) := isAlgebraicSpace_yoneda B S hS Y₁
  have hPalg : IsAlgebraicSpace B S hS (pullback q₁ f) :=
    isAlgebraicSpace_pullback B S hS q₁ f hY₁alg hX hY
  have hPqc : IsQuasiCompactSpace B S hS (pullback q₁ f) :=
    hf.2 (yoneda.obj Y₁) hY₁alg (isQuasiCompactSpace_yoneda_of_isAffine B S hS Y₁ hY₁aff) q₁
  -- Stacks 03H6: an affine surjective étale cover `c : X' ⟶ X ×_Y Y₁`.
  have hc' := (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (pullback q₁ f) hPalg).mp hPqc
  obtain ⟨X', c, hX'aff, hcsurj, hcet⟩ := hc'
  have hcP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c :=
    (isEtale_iff_presheaf_of_yoneda B S hS c).1 hcet
  have hsndP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd q₁ f) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback q₁ f) hq₁et
  have _ : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
    inverseImage_isStableUnderComposition B S hS etale_isStableUnderComposition.{u}
  have hUP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (c ≫ pullback.snd q₁ f) :=
    (MorphismProperty.relative_isStableUnderComposition _).comp_mem _ _ hcP hsndP
  -- The affine étale chart `U = X'` of `X`, with its morphism `ĝ` to `Y₁`.
  let U : SmallEtale B S hS X := ⟨CostructuredArrow.mk (c ≫ pullback.snd q₁ f), hUP⟩
  let ĝ : U.obj.left ⟶ Y₁ := yoneda.preimage (c ≫ pullback.fst q₁ f)
  have hĝmap : yoneda.map ĝ = c ≫ pullback.fst q₁ f := yoneda.map_preimage _
  have hsq : yoneda.map ĝ ≫ q₁ = U.obj.hom ≫ f := by
    rw [hĝmap]
    show (c ≫ pullback.fst q₁ f) ≫ q₁ = (c ≫ pullback.snd q₁ f) ≫ f
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hlft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map ĝ) :=
    hf.1 U.obj.left Y₁ U.obj.hom q₁ ĝ hUP hq₁et hsq
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj Y₁) := hY₁aff
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj U.obj.left) := hX'aff
  have hqc : ∀ V : SmallEtale B S hS X, (restrictToChart B S hS hX F V).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS ⟨X, hX⟩ F hFq
  have hfc : ∀ V : SmallEtale B S hS X, (restrictToChart B S hS hX F V).IsFiniteType :=
    isFiniteType_restrictToChart B S hS ⟨X, hX⟩ F hFq hFt
  let G := restrictToChart B S hS hX F U
  have _ : G.IsQuasicoherent := hqc U
  have _ : G.IsFiniteType := hfc U
  -- Stacks 05HU at the chart, with an affine neighbourhood and affine sources.
  have h05 := exists_isAffine_etaleNeighborhood_completeDevissage_affineCover
    ((BigFppfOver.toScheme B S hS).map ĝ) G (pointsToScheme B S hS Y₁ w)
  obtain ⟨S', -, hS'aff, n, A, hA, e, he, hl, hq, ht, hD, hcov⟩ := h05
  -- The affine neighbourhood `S'` is an object `Y'` of the site, étale over `Y₁` and hence over
  -- `Y`, and its distinguished point is a point `y'` of `Y'` over `y`.
  have hS'c : B.Contains S'.scheme :=
    (Scheme.size_le_of_locallyOfFiniteType S'.toBase).trans_lt Y₁.left.property
  let Y' : BigFppfOver B S hS := siteObject B S hS hS'c (S'.toBase ≫ B.inclusion.map Y₁.hom)
  let ι' : Y' ⟶ Y₁ := Over.homMk (ObjectProperty.homMk S'.toBase) rfl
  have hι' : (BigFppfOver.toScheme B S hS).map ι' = S'.toBase := rfl
  have _ : Etale ((BigFppfOver.toScheme B S hS).map ι') := by
    rw [hι']
    infer_instance
  let y' : points B S hS (yoneda.obj Y') := (pointsEquivScheme B S hS Y').symm S'.point
  have hy'pt : pointsToScheme B S hS Y' y' = S'.point :=
    (pointsEquivScheme B S hS Y').apply_symm_apply S'.point
  have hy'w : pointsMap B S hS _ (yoneda.map ι') y' = w := by
    refine injective_pointsToScheme B S hS Y₁ ?_
    rw [pointsToScheme_pointsMap_yoneda, hy'pt, hι']
    exact S'.map_point
  let q : yoneda.obj Y' ⟶ Y := yoneda.map ι' ≫ q₁
  have hqP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf q :=
    etale_comp_of_scheme B S hS ι' q₁ inferInstance hq₁et
  refine ⟨Y', q, y', hS'aff, (isEtale_iff_presheaf_of_yoneda B S hS q).2 hqP, ?_, ?_⟩
  · rw [pointsMap_comp_apply, hy'w, hw]
  -- The chart `U ×_{Y₁} Y'` of `X ×_Y Y'`: it is the base change of `c`.
  have hcond : yoneda.map (pullback.snd ĝ ι') ≫ q =
      yoneda.map (pullback.fst ĝ ι') ≫ U.obj.hom ≫ f := by
    show yoneda.map (pullback.snd ĝ ι') ≫ yoneda.map ι' ≫ q₁ = _
    rw [← Category.assoc, ← yoneda.map_comp, ← pullback.condition, yoneda.map_comp,
      Category.assoc, hsq]
  let φ : yoneda.obj (pullback ĝ ι') ⟶ pullback q f :=
    pullback.lift (yoneda.map (pullback.snd ĝ ι')) (yoneda.map (pullback.fst ĝ ι') ≫ U.obj.hom)
      hcond
  let ψ : pullback q f ⟶ pullback q₁ f :=
    pullback.lift (pullback.fst q f ≫ yoneda.map ι') (pullback.snd q f)
      (by rw [Category.assoc, ← pullback.condition])
  have hφfst : φ ≫ pullback.fst q f = yoneda.map (pullback.snd ĝ ι') := pullback.lift_fst _ _ _
  have hφsnd : φ ≫ pullback.snd q f = yoneda.map (pullback.fst ĝ ι') ≫ U.obj.hom :=
    pullback.lift_snd _ _ _
  have hsq' : IsPullback (yoneda.map (pullback.fst ĝ ι')) φ c ψ :=
    isPullback_yoneda_pullback_baseChange B S hS f q₁ c ĝ hĝmap ι' φ hφfst hφsnd ψ
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hφP : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf φ :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq' hcP
  have hφsurj : IsSurjective B S hS φ :=
    isSurjective_of_presheafSurjective B S hS φ
      ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hsq' hcsurj)
  -- The pieces of the cover, as objects of the site.
  have hpc := exists_siteObjects_completeDevissage_cover B S hS ĝ ι' G S'.point A hA e he
    hl hq ht hD hcov
  obtain ⟨Wo, b, a, k, hkb, hka, hkE, hbE, hl', hq', ht', hD', hcov'⟩ := hpc
  let hmor : ∀ i, yoneda.obj (Wo i) ⟶ pullback q f := fun i => yoneda.map (k i) ≫ φ
  have hfst : ∀ i, hmor i ≫ pullback.fst q f = yoneda.map (a i) := fun i => by
    show (yoneda.map (k i) ≫ φ) ≫ _ = _
    rw [Category.assoc, hφfst, ← yoneda.map_comp, hka]
  have hsnd : ∀ i, hmor i ≫ pullback.snd q f = yoneda.map (b i) ≫ U.obj.hom := fun i => by
    show (yoneda.map (k i) ≫ φ) ≫ _ = _
    rw [Category.assoc, hφsnd, ← Category.assoc, ← yoneda.map_comp, hkb]
  have hWc : ∀ i, IsEtaleChart B S hS X (CostructuredArrow.mk (hmor i ≫ pullback.snd q f)) :=
    fun i => by
      show (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (hmor i ≫ pullback.snd q f)
      rw [hsnd]
      exact etale_comp_of_scheme B S hS (b i) U.obj.hom (hbE i) U.property
  refine ⟨n, Wo, hmor, fun i => (isEtale_iff_presheaf_of_yoneda B S hS _).2
    (etale_comp_of_scheme B S hS (k i) φ (hkE i) hφP), hWc, a, hfst, hl',
    fun i => hqc _, fun i => hfc _, ?_, ?_⟩
  · intro i
    -- The restriction of `F` to the chart is the pullback of its restriction to `U`.
    let Wc : SmallEtale B S hS X := ⟨CostructuredArrow.mk (hmor i ≫ pullback.snd q f), hWc i⟩
    let β : Wc ⟶ U := ObjectProperty.homMk (CostructuredArrow.homMk (b i) (hsnd i).symm)
    obtain ⟨e₂⟩ := nonempty_restrictToChartScheme_chartBaseChange B S hS ⟨X, hX⟩ F hFq β
    let eMod : restrictToChart B S hS hX F Wc ≅
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map (b i))).obj G :=
      restrictToChartIsoRestrictToChartScheme B S hS hX F Wc ≪≫ e₂.symm ≪≫
        ((Scheme.Modules.pullback (chartSchemeMap β)).mapIso
          (restrictToChartIsoRestrictToChartScheme B S hS hX F U)).symm
    have := hl' i
    have := hq' i
    have := ht' i
    have := hqc Wc
    have := hfc Wc
    rw [hy'pt]
    obtain ⟨D⟩ := hD' i
    exact ⟨D.ofModuleIso eMod⟩
  · intro x hx
    obtain ⟨p, hp⟩ := hφsurj x
    have hpt : (BigFppfOver.toScheme B S hS).map (pullback.snd ĝ ι')
        (pointsToScheme B S hS _ p) = S'.point := by
      rw [← pointsToScheme_pointsMap_yoneda, ← hφfst, pointsMap_comp_apply, hp, hx, hy'pt]
    obtain ⟨i, w', hw'⟩ := hcov' _ hpt
    refine ⟨i, (pointsEquivScheme B S hS (Wo i)).symm w', ?_⟩
    have hk' : pointsMap B S hS _ (yoneda.map (k i))
        ((pointsEquivScheme B S hS (Wo i)).symm w') = p := by
      refine injective_pointsToScheme B S hS _ ?_
      rw [pointsToScheme_pointsMap_yoneda,
        show pointsToScheme B S hS (Wo i) ((pointsEquivScheme B S hS (Wo i)).symm w') = w' from
          (pointsEquivScheme B S hS (Wo i)).apply_symm_apply w', hw']
    show pointsMap B S hS _ (yoneda.map (k i) ≫ φ) _ = x
    rw [pointsMap_comp_apply, hk', hp]

end AlgebraicGeometry.Space

end
