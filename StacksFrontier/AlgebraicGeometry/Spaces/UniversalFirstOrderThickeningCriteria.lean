module

public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleIdealSheafRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Universal

/-!
# Testing the universal first-order thickening property on schemes

Let `Z ⊂ Z'` be a first-order thickening of algebraic spaces over a scheme `S`, equipped with
a morphism `p : Z' ⟶ X` to an algebraic space.  Being a *universal* first-order thickening,
`AlgebraicGeometry.Space.IsUniversalFirstOrderThickening`, is the requirement that every solid
diagram of Stacks 0602 built from a first-order thickening `T ⊂ T'` of algebraic spaces admits a
unique dotted arrow.  This file shows that it is enough to test the diagrams whose ambient test
object `T'` is a *scheme*.

## Main definitions

* `AlgebraicGeometry.Space.HasRepresentableLiftingProperty`: **Stacks 0603**, part (2), the
  lifting property tested only on the diagrams whose ambient test object is a scheme.
* `AlgebraicGeometry.Space.HasAffineLiftingProperty`: **Stacks 0603**, part (3), the same tested
  only on affine schemes.

## Main results

* `AlgebraicGeometry.Space.isUniversalFirstOrderThickening_iff_representable`: **Stacks 0603**,
  the equivalence of parts (1) and (2).
* `AlgebraicGeometry.Space.HasRepresentableLiftingProperty.hasAffineLiftingProperty`:
  **Stacks 0603**, the implication from part (2) to part (3).
* `AlgebraicGeometry.Space.isNthOrderThickening_preimage_of_isEtale` and
  `AlgebraicGeometry.Space.isFirstOrderThickening_preimage_of_isEtale`: the inverse image of an
  `n`th-order thickening along an étale morphism of algebraic spaces is an `n`th-order
  thickening.

## Implementation notes

"`T'` is a scheme" is `CategoryTheory.Functor.IsRepresentable` of the presheaf underlying `T'`,
and "`T'` is an affine scheme" is `AlgebraicGeometry.Space.IsAffineSpace`. The test objects
range over the algebraic spaces over `S` of `AlgebraicGeometry.AlgebraicSpaces`, which is pinned
to one big fppf site `B` and one base scheme `S`, so "scheme" means an object of that site, as
in `AlgebraicGeometry.Space.IsUniversalFirstOrderThickening` itself.

The converse to part (2) descends a dotted arrow along a surjective étale chart `U ⟶ T'` by a
scheme, which exhibits `T'` as the coequalizer of `U ×_{T'} U ⇉ U` in fppf sheaves
(`AlgebraicGeometry.Space.isCoequalizer_of_surjectiveEtale`).

## References

* [Stacks Project, Tag 0603](https://stacks.math.columbia.edu/tag/0603)
* [Stacks Project, Tag 0602](https://stacks.math.columbia.edu/tag/0602)
* [Stacks Project, Tag 09ZX](https://stacks.math.columbia.edu/tag/09ZX)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Thickenings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Inverse images of thickenings along an étale morphism -/

/-- **The inverse image of an `n`th-order thickening along an étale morphism is an `n`th-order
thickening.** For `f : X' ⟶ Y'` étale and `Y ⊂ Y'` an `n`th-order thickening, the inverse image
`Y ×_{Y'} X' ⊂ X'` is an `n`th-order thickening. -/
theorem isNthOrderThickening_preimage_of_isEtale {n : ℕ} {Y' X' : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (f : X' ⟶ Y') (hf : IsEtale B S hS f.hom)
    (hY : IsNthOrderThickening B S hS n Y' Y) :
    IsNthOrderThickening B S hS n X' (Y.preimage f.hom) := by
  refine ⟨isThickening_preimage B S hS Y f hY.1, fun V ↦ ?_⟩
  rw [definingIdealAt_preimage_eq_definingIdealAt_postcomp B S hS f hf ⟨Y, hY.1.1⟩ V]
  exact hY.2 _

/-- **The inverse image of a first-order thickening along an étale morphism is a first-order
thickening.** The case `n = 1` of
`AlgebraicGeometry.Space.isNthOrderThickening_preimage_of_isEtale`. -/
theorem isFirstOrderThickening_preimage_of_isEtale {Y' X' : AlgebraicSpaces B S hS}
    (Y : Subfunctor Y'.1) (f : X' ⟶ Y') (hf : IsEtale B S hS f.hom)
    (hY : IsFirstOrderThickening B S hS Y' Y) :
    IsFirstOrderThickening B S hS X' (Y.preimage f.hom) :=
  isNthOrderThickening_preimage_of_isEtale B S hS Y f hf hY

/-! ### Epimorphisms of sheaves out of a surjective étale chart -/

/-- A surjective étale chart of an algebraic space is an epimorphism of fppf sheaves: two
morphisms from that algebraic space to an fppf sheaf agree as soon as they agree after the
chart. -/
theorem eq_of_comp_eq_of_surjectiveEtale
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ F)
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) φ)
    {w₁ w₂ : F ⟶ G} (hw : φ ≫ w₁ = φ ≫ w₂) : w₁ = w₂ := by
  have hrep : yoneda.relativelyRepresentable φ := hetale.1
  obtain ⟨hRsh, hVsh, ⟨hcol⟩⟩ := isCoequalizer_of_surjectiveEtale B S hS φ
    (hrep.fst' φ) (hrep.snd φ) (hrep.isPullback' φ) hF hsurj hetale
  let J := BigFppfOver.topology B S hS
  let VF : Sheaf J (Type u) := ⟨yoneda.obj V, hVsh⟩
  let FF : Sheaf J (Type u) := ⟨F, hF.isSheaf⟩
  let GF : Sheaf J (Type u) := ⟨G, hG⟩
  let ff : VF ⟶ FF := ObjectProperty.homMk φ
  have : Epi ff := Cofork.IsColimit.epi hcol
  have hsheaf : (ObjectProperty.homMk w₁ : FF ⟶ GF) = ObjectProperty.homMk w₂ :=
    (cancel_epi ff).1 (Sheaf.hom_ext hw)
  exact congrArg (fun k : FF ⟶ GF ↦ k.hom) hsheaf

/-- Surjectivity after every representable base change is stable under composition. -/
theorem isStableUnderComposition_presheaf_surjective :
    MorphismProperty.IsStableUnderComposition
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
  have : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    (inferInstance : MorphismProperty.IsMultiplicative
      (@Surjective.{u} : MorphismProperty Scheme.{u})).toIsStableUnderComposition
  have : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  MorphismProperty.relative_isStableUnderComposition _

/-! ### Testing the universal property on schemes -/

section Criterion

variable {X Z' : AlgebraicSpaces B S hS} (Z : Subfunctor Z'.1) (p : Z' ⟶ X)

/-- The lifting property of the diagrams of Stacks 0602 whose ambient test object `T'` is a
scheme, that is, whose underlying presheaf is representable. -/
@[stacks 0603 "part (2), the lifting property tested on schemes"]
def HasRepresentableLiftingProperty : Prop :=
  ∀ {T' : AlgebraicSpaces B S hS}, T'.1.IsRepresentable → ∀ T : Subfunctor T'.1,
    IsFirstOrderThickening B S hS T' T →
    ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
      T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
      ∃! c : T'.1 ⟶ Z'.1, T.ι ≫ c = a ≫ Z.ι ∧ c ≫ p.hom = b

/-- The lifting property of the diagrams of Stacks 0602 whose ambient test object `T'` is an
affine scheme. -/
@[stacks 0603 "part (3), the lifting property tested on affine schemes"]
def HasAffineLiftingProperty : Prop :=
  ∀ {T' : AlgebraicSpaces B S hS}, IsAffineSpace B S hS T'.1 → ∀ T : Subfunctor T'.1,
    IsFirstOrderThickening B S hS T' T →
    ∀ (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1),
      T.ι ≫ b = a ≫ Z.ι ≫ p.hom →
      ∃! c : T'.1 ⟶ Z'.1, T.ι ≫ c = a ≫ Z.ι ∧ c ≫ p.hom = b

variable {Z p}

/-- A commuting square over `T ⊂ T'` restricts along `f` to a commuting square over the inverse
image of `T`. -/
private theorem preimage_ι_comp_comp {P Q G W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : Subfunctor Q) (f : P ⟶ Q) (w : Q ⟶ W) (a : T.toFunctor ⟶ G) (v : G ⟶ W)
    (h : T.ι ≫ w = a ≫ v) : (T.preimage f).ι ≫ f ≫ w = (T.fromPreimage f ≫ a) ≫ v := by
  rw [← Subfunctor.fromPreimage_ι_assoc, h, Category.assoc]

/-- Given `AlgebraicGeometry.Space.HasRepresentableLiftingProperty`, the restriction of a solid
diagram along an étale morphism `φ : V ⟶ T'` from a scheme has a unique dotted arrow. -/
private theorem exists_lift_along_etale (h : HasRepresentableLiftingProperty B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom)
    {V : BigFppfOver B S hS} (φ : yoneda.obj V ⟶ T'.1) (hφ : IsEtale B S hS φ) :
    ∃! c : yoneda.obj V ⟶ Z'.1,
      (T.preimage φ).ι ≫ c = (T.fromPreimage φ ≫ a) ≫ Z.ι ∧ c ≫ p.hom = φ ≫ b := by
  exact h (T' := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩) inferInstance
    (T.preimage φ) (isFirstOrderThickening_preimage_of_isEtale B S hS T _ hφ hT)
    (T.fromPreimage φ ≫ a) (φ ≫ b) (preimage_ι_comp_comp B S hS T φ b a _ comm)

/-- **The chart-level dotted arrow is compatible with the kernel pair of the chart.** If `l` is
the dotted arrow over an étale chart `f : U ⟶ T'` of the ambient test space and `s, t : R ⇉ U`
are the two projections of the kernel pair of `f`, then `s ≫ l = t ≫ l`. -/
private theorem comp_eq_comp_of_representableLifting
    (h : HasRepresentableLiftingProperty B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom)
    {U R : BigFppfOver B S hS} (f : yoneda.obj U ⟶ T'.1) (s t : R ⟶ U)
    (hpb : IsPullback (yoneda.map s) (yoneda.map t) f f)
    (hsEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) (yoneda.map s))
    (hfEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f) {l : yoneda.obj U ⟶ Z'.1}
    (hl₁ : (T.preimage f).ι ≫ l = (T.fromPreimage f ≫ a) ≫ Z.ι)
    (hl₂ : l ≫ p.hom = f ≫ b) :
    yoneda.map s ≫ l = yoneda.map t ≫ l := by
  have hcompE := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  have hsfEtale : IsEtale B S hS (yoneda.map s ≫ f) :=
    isEtale_of_presheaf_etale B S hS (MorphismProperty.comp_mem _ _ _ hsEtale hfEtale)
  obtain ⟨c₀, -, huniq⟩ :=
    exists_lift_along_etale B S hS h T hT a b comm (yoneda.map s ≫ f) hsfEtale
  have hpre : T.preimage (yoneda.map s ≫ f) = (T.preimage f).preimage (yoneda.map s) :=
    Subfunctor.preimage_comp T _ _
  obtain ⟨qS, hqS⟩ : ∃ q : (T.preimage (yoneda.map s ≫ f)).toFunctor ⟶
      (T.preimage f).toFunctor,
      q ≫ (T.preimage f).ι = (T.preimage (yoneda.map s ≫ f)).ι ≫ yoneda.map s :=
    ⟨Subfunctor.lift ((T.preimage (yoneda.map s ≫ f)).ι ≫ yoneda.map s) (by
      rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff, ← hpre]), rfl⟩
  obtain ⟨qT, hqT⟩ : ∃ q : (T.preimage (yoneda.map s ≫ f)).toFunctor ⟶
      (T.preimage f).toFunctor,
      q ≫ (T.preimage f).ι = (T.preimage (yoneda.map s ≫ f)).ι ≫ yoneda.map t :=
    ⟨Subfunctor.lift ((T.preimage (yoneda.map s ≫ f)).ι ≫ yoneda.map t) (by
      rw [Subfunctor.range_comp, Subfunctor.range_ι, Subfunctor.image_le_iff,
        ← Subfunctor.preimage_comp, hpb.w]), rfl⟩
  have hqSa : qS ≫ T.fromPreimage f = T.fromPreimage (yoneda.map s ≫ f) := by
    apply (cancel_mono T.ι).1
    rw [Category.assoc, Subfunctor.fromPreimage_ι, Subfunctor.fromPreimage_ι,
      ← Category.assoc, hqS, Category.assoc]
  have hqTa : qT ≫ T.fromPreimage f = T.fromPreimage (yoneda.map s ≫ f) := by
    apply (cancel_mono T.ι).1
    rw [Category.assoc, Subfunctor.fromPreimage_ι, Subfunctor.fromPreimage_ι,
      ← Category.assoc, hqT, Category.assoc, ← hpb.w]
  have key : ∀ (u : R ⟶ U) (q : (T.preimage (yoneda.map s ≫ f)).toFunctor ⟶
        (T.preimage f).toFunctor),
      q ≫ (T.preimage f).ι = (T.preimage (yoneda.map s ≫ f)).ι ≫ yoneda.map u →
      q ≫ T.fromPreimage f = T.fromPreimage (yoneda.map s ≫ f) →
      yoneda.map u ≫ f = yoneda.map s ≫ f →
      (T.preimage (yoneda.map s ≫ f)).ι ≫ (yoneda.map u ≫ l) =
          (T.fromPreimage (yoneda.map s ≫ f) ≫ a) ≫ Z.ι ∧
        (yoneda.map u ≫ l) ≫ p.hom = (yoneda.map s ≫ f) ≫ b := by
    intro u q hq hqa hu
    refine ⟨?_, ?_⟩
    · calc (T.preimage (yoneda.map s ≫ f)).ι ≫ yoneda.map u ≫ l
          = (q ≫ (T.preimage f).ι) ≫ l := by rw [hq, Category.assoc]
        _ = q ≫ (T.fromPreimage f ≫ a) ≫ Z.ι := by rw [Category.assoc, hl₁]
        _ = ((q ≫ T.fromPreimage f) ≫ a) ≫ Z.ι := by simp only [Category.assoc]
        _ = (T.fromPreimage (yoneda.map s ≫ f) ≫ a) ≫ Z.ι := by rw [hqa]
    · calc (yoneda.map u ≫ l) ≫ p.hom = yoneda.map u ≫ f ≫ b := by rw [Category.assoc, hl₂]
        _ = (yoneda.map s ≫ f) ≫ b := by rw [← Category.assoc, hu]
  exact (huniq _ (key s qS hqS hqSa rfl)).trans (huniq _ (key t qT hqT hqTa hpb.w.symm)).symm

/-- **The dotted arrow exists, given part (2) of Stacks 0603.** Under
`AlgebraicGeometry.Space.HasRepresentableLiftingProperty`, every solid diagram of Stacks 0602
over a first-order thickening `T ⊂ T'` of algebraic spaces has a dotted arrow. -/
private theorem exists_lift_of_representableLifting
    (h : HasRepresentableLiftingProperty B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom) :
    ∃ c : T'.1 ⟶ Z'.1, T.ι ≫ c = a ≫ Z.ι ∧ c ≫ p.hom = b := by
  obtain ⟨U, f, hsurj, hetale⟩ := T'.2.exists_atlas
  have hrep : yoneda.relativelyRepresentable f := hetale.1
  have hfEtale : IsEtale B S hS f := isEtale_of_presheaf_etale B S hS hetale
  obtain ⟨R, s, t, hpb, hsEtale⟩ :
      ∃ (R : BigFppfOver B S hS) (s t : R ⟶ U),
        IsPullback (yoneda.map s) (yoneda.map t) f f ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) (yoneda.map s) :=
    ⟨hrep.pullback f, hrep.snd f, hrep.fst' f, (hrep.isPullback' f).flip,
      (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
        (@Etale.{u} : MorphismProperty Scheme.{u}) (hrep.snd f)).2
        (hetale.2 f (hrep.fst f) (hrep.snd f) (hrep.isPullback f))⟩
  obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := exists_lift_along_etale B S hS h T hT a b comm f hfEtale
  have hcompat := comp_eq_comp_of_representableLifting B S hS h T hT a b comm f s t hpb
    hsEtale hetale hl₁ hl₂
  obtain ⟨hRsh, hUsh, ⟨hcoeq⟩⟩ :=
    isCoequalizer_of_surjectiveEtale B S hS f s t hpb T'.2 hsurj hetale
  let J := BigFppfOver.topology B S hS
  let UF : Sheaf J (Type u) := ⟨yoneda.obj U, hUsh⟩
  let RF : Sheaf J (Type u) := ⟨yoneda.obj R, hRsh⟩
  let TF : Sheaf J (Type u) := ⟨T'.1, T'.2.isSheaf⟩
  let ZF : Sheaf J (Type u) := ⟨Z'.1, Z'.2.isSheaf⟩
  let sf : RF ⟶ UF := ObjectProperty.homMk (yoneda.map s)
  let tf : RF ⟶ UF := ObjectProperty.homMk (yoneda.map t)
  let ff : UF ⟶ TF := ObjectProperty.homMk f
  have hw : sf ≫ ff = tf ≫ ff := Sheaf.hom_ext hpb.w
  have hcol : IsColimit (Cofork.ofπ ff hw) := hcoeq
  have hlw : sf ≫ (ObjectProperty.homMk l : UF ⟶ ZF) = tf ≫ ObjectProperty.homMk l :=
    Sheaf.hom_ext hcompat
  have hfac : f ≫ (hcol.desc (Cofork.ofπ (ObjectProperty.homMk l : UF ⟶ ZF) hlw)).hom = l :=
    congrArg (fun k : UF ⟶ ZF ↦ k.hom)
      (hcol.fac (Cofork.ofπ (ObjectProperty.homMk l : UF ⟶ ZF) hlw) WalkingParallelPair.one)
  refine ⟨(hcol.desc (Cofork.ofπ (ObjectProperty.homMk l : UF ⟶ ZF) hlw)).hom, ?_, ?_⟩
  · have hTU := isFirstOrderThickening_preimage_of_isEtale B S hS T
      (ObjectProperty.homMk f : (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ :
        AlgebraicSpaces B S hS) ⟶ T') hfEtale hT
    obtain ⟨V, e, heSurj, heEtale⟩ := hTU.1.1.1.exists_atlas
    have hqSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (T.fromPreimage f) :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (Subfunctor.isPullback_preimage f T).flip hsurj
    have hqEtale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (T.fromPreimage f) :=
      (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
        (Subfunctor.isPullback_preimage f T).flip hetale
    have hcompS := isStableUnderComposition_presheaf_surjective B S hS
    have hcompE := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
    refine eq_of_comp_eq_of_surjectiveEtale B S hS hT.1.1.1 Z'.2.isSheaf
      (e ≫ T.fromPreimage f) (MorphismProperty.comp_mem _ _ _ heSurj hqSurj)
      (MorphismProperty.comp_mem _ _ _ heEtale hqEtale) ?_
    calc (e ≫ T.fromPreimage f) ≫ T.ι ≫
            (hcol.desc (Cofork.ofπ (ObjectProperty.homMk l : UF ⟶ ZF) hlw)).hom
        = e ≫ (T.preimage f).ι ≫ f ≫
            (hcol.desc (Cofork.ofπ (ObjectProperty.homMk l : UF ⟶ ZF) hlw)).hom := by
          rw [Category.assoc, Subfunctor.fromPreimage_ι_assoc]
      _ = e ≫ (T.preimage f).ι ≫ l := by rw [hfac]
      _ = (e ≫ T.fromPreimage f) ≫ a ≫ Z.ι := by
          rw [hl₁]
          simp only [Category.assoc]
  · refine eq_of_comp_eq_of_surjectiveEtale B S hS T'.2 X.2.isSheaf f hsurj hetale ?_
    rw [← Category.assoc, hfac, hl₂]

/-- **The dotted arrow is unique, given part (2) of Stacks 0603.** Under
`AlgebraicGeometry.Space.HasRepresentableLiftingProperty`, two dotted arrows for a solid diagram
of Stacks 0602 over a first-order thickening `T ⊂ T'` of algebraic spaces are equal. -/
private theorem lift_unique_of_representableLifting
    (h : HasRepresentableLiftingProperty B S hS Z p)
    {T' : AlgebraicSpaces B S hS} (T : Subfunctor T'.1)
    (hT : IsFirstOrderThickening B S hS T' T)
    (a : T.toFunctor ⟶ Z.toFunctor) (b : T'.1 ⟶ X.1)
    (comm : T.ι ≫ b = a ≫ Z.ι ≫ p.hom) (c d : T'.1 ⟶ Z'.1)
    (hc : T.ι ≫ c = a ≫ Z.ι ∧ c ≫ p.hom = b)
    (hd : T.ι ≫ d = a ≫ Z.ι ∧ d ≫ p.hom = b) : c = d := by
  obtain ⟨U, f, hsurj, hetale⟩ := T'.2.exists_atlas
  have hfEtale : IsEtale B S hS f := isEtale_of_presheaf_etale B S hS hetale
  obtain ⟨c₀, -, huniq⟩ := exists_lift_along_etale B S hS h T hT a b comm f hfEtale
  have key : ∀ w : T'.1 ⟶ Z'.1, T.ι ≫ w = a ≫ Z.ι → w ≫ p.hom = b →
      (T.preimage f).ι ≫ (f ≫ w) = (T.fromPreimage f ≫ a) ≫ Z.ι ∧
        (f ≫ w) ≫ p.hom = f ≫ b := by
    intro w h₁ h₂
    exact ⟨preimage_ι_comp_comp B S hS T f w a _ h₁, by rw [Category.assoc, h₂]⟩
  exact eq_of_comp_eq_of_surjectiveEtale B S hS T'.2 Z'.2.isSheaf f hsurj hetale
    ((huniq _ (key c hc.1 hc.2)).trans (huniq _ (key d hd.1 hd.2)).symm)

/-! ### Stacks 0603 -/

/-- A first-order thickening `Z ⊂ Z'` of algebraic spaces over `X` is a universal first-order
thickening if and only if the dotted arrow of the diagram of Stacks 0602 exists and is unique for
every test thickening `T ⊂ T'` whose ambient space `T'` is a *scheme*. -/
@[stacks 0603 "equivalence of (1) and (2)"]
theorem isUniversalFirstOrderThickening_iff_representable
    (hZ : IsFirstOrderThickening B S hS Z' Z) :
    IsUniversalFirstOrderThickening B S hS Z p ↔
      HasRepresentableLiftingProperty B S hS Z p := by
  refine ⟨fun hu _ _ T hT a b hab ↦ hu.existsUnique_lift T hT a b hab, fun h ↦ ⟨hZ, ?_⟩⟩
  intro T' T hT a b hab
  obtain ⟨c, hc⟩ := exists_lift_of_representableLifting B S hS h T hT a b hab
  exact ⟨c, hc, fun d hd ↦
    lift_unique_of_representableLifting B S hS h T hT a b hab d c hd hc⟩

/-- The lifting property of the diagrams of Stacks 0602 tested on schemes implies the same
property tested on affine schemes. -/
@[stacks 0603 "(2) implies (3)"]
theorem HasRepresentableLiftingProperty.hasAffineLiftingProperty
    (h : HasRepresentableLiftingProperty B S hS Z p) :
    HasAffineLiftingProperty B S hS Z p := by
  intro T' hT' T hT a b hab
  obtain ⟨W, -, ⟨i⟩⟩ := hT'
  exact h (Functor.IsRepresentable.mk' i.symm) T hT a b hab

end Criterion

end AlgebraicGeometry.Space

end
