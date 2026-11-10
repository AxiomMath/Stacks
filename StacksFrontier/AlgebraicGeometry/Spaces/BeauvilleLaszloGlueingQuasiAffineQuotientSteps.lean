module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineFlatPresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuasiAffineQuotientAux
public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingQuotient
public import StacksFrontier.CategoryTheory.EquivalenceRelation.Transfer
import all StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingFullyFaithful

/-!
# The quotient step of Stacks 0F9U, in general form

Three statements the proof of Stacks 0F9U uses after the relation `W ⇉ T` has been produced, each
proved here in the generality of an arbitrary square and gluing functor, where it is pure
bookkeeping:

* an internal equivalence relation is carried by a functor to one, given the image of its
  fibre product and joint monicity of the image pair;
* a closed immersion: the base change of `(p₀, p₁) : W ⟶ T ⨯ T` is a closed immersion as soon
  as the base changes of `p₀, p₁` are the kernel pair of a morphism to a separated space;
* the realization: if the base changes of a quotient map `π : T ⟶ Y` are universal for maps
  coequalizing the base changes of `p₀, p₁`, and the latter are, leg by leg, the kernel pair of a
  locally surjective component of a morphism of triples `G(T) ⟶ Z`, then `G(Y) ≅ Z`.

## Main results

* `CategoryTheory.isEquivalenceRelation_map_of_isPullback`
* `BeauvilleLaszlo.Space.isClosedImmersion_baseChange_map_prodLift`
* `BeauvilleLaszlo.Space.exists_iso_of_quotient_leg`
* `BeauvilleLaszlo.Space.nonempty_glueingFunctor_iso_of_quotient`

## References

* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace CategoryTheory

/-- **An internal equivalence relation is carried by a functor to one**, given that the functor
sends the fibre product of the pair to a fibre product and the image pair is jointly monic. No
preservation of limits is asked of the functor beyond this one fibre product. -/
theorem isEquivalenceRelation_map_of_isPullback {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {R X : C} {p₀ p₁ : R ⟶ X} (e : EquivalenceRelation p₀ p₁) [HasPullback p₁ p₀]
    (hpb : IsPullback (F.map (pullback.fst p₁ p₀)) (F.map (pullback.snd p₁ p₀)) (F.map p₁)
      (F.map p₀))
    (hmono : JointlyMono₂ (F.map p₀) (F.map p₁)) :
    IsEquivalenceRelation (F.map p₀) (F.map p₁) := by
  let i := e.isLimit.conePointUniqueUpToIso (pullback.isLimit p₁ p₀)
  have hfst : i.inv ≫ e.c.fst = pullback.fst p₁ p₀ :=
    e.isLimit.conePointUniqueUpToIso_inv_comp (pullback.isLimit p₁ p₀) WalkingCospan.left
  have hsnd : i.inv ≫ e.c.snd = pullback.snd p₁ p₀ :=
    e.isLimit.conePointUniqueUpToIso_inv_comp (pullback.isLimit p₁ p₀) WalkingCospan.right
  refine EquivalenceRelation.isEquivalenceRelation
    { right_cancellation := hmono.right_cancellation
      r := F.map e.r
      reflexivity₁ := by rw [← F.map_comp, e.reflexivity₁, F.map_id]
      reflexivity₂ := by rw [← F.map_comp, e.reflexivity₂, F.map_id]
      s := F.map e.s
      symmetry₁ := by rw [← F.map_comp, e.symmetry₁]
      symmetry₂ := by rw [← F.map_comp, e.symmetry₂]
      c := hpb.cone
      isLimit := hpb.isLimit
      t := F.map (i.inv ≫ e.t)
      transitivity₁ := ?_
      transitivity₂ := ?_ }
  · change F.map (i.inv ≫ e.t) ≫ F.map p₀ = F.map (pullback.fst p₁ p₀) ≫ F.map p₀
    rw [← F.map_comp, ← F.map_comp, Category.assoc, e.transitivity₁, ← Category.assoc, hfst]
  · change F.map (i.inv ≫ e.t) ≫ F.map p₁ = F.map (pullback.snd p₁ p₀) ≫ F.map p₁
    rw [← F.map_comp, ← F.map_comp, Category.assoc, e.transitivity₂, ← Category.assoc, hsnd]

end CategoryTheory

namespace BeauvilleLaszlo.Space

attribute [local instance] spaces_inclusion_preservesPullback

/-! ### The closed immersion -/

section ClosedImmersion

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS' ⟶ B.obj hS)

/-- **The base change of `(p₀, p₁)` is a closed immersion** when the base changes of `p₀` and
`p₁` are the kernel pair of a morphism `φ'` to a space separated over the base: it is then the
base change of the diagonal of that space along `φ' ⨯ φ'`. -/
theorem isClosedImmersion_baseChange_map_prodLift {W T : AlgebraicSpaces B S hS}
    (p₀ p₁ : W ⟶ T) {Z' : AlgebraicSpaces B S' hS'}
    (φ' : (baseChange B S' S hS' hS g).obj T ⟶ Z')
    (hk : IsPullback ((baseChange B S' S hS' hS g).map p₀)
      ((baseChange B S' S hS' hS g).map p₁) φ' φ')
    (hsep : AlgebraicGeometry.Space.IsSeparatedOver B S' hS' Z'.obj) :
    AlgebraicGeometry.Space.IsClosedImmersion B S' hS'
      ((baseChange B S' S hS' hS g).map
        (ObjectProperty.homMk (prod.lift p₀.hom p₁.hom) :
          W ⟶ AlgebraicGeometry.AlgebraicSpaces.product B S hS T T)).hom := by
  let P := MorphismProperty.inverseImage (@AlgebraicGeometry.IsClosedImmersion.{u})
    (BigFppfOver.toScheme B S' hS')
  have hP : P.presheaf.RespectsIso := MorphismProperty.relative_respectsIso _
  have hPb : P.presheaf.IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange P
  let rR := OverShriek.relocalizeRestrict g
  let bc := baseChange B S' S hS' hS g
  -- the kernel pair of `φ'` is a closed subspace of the product
  have hker : P.presheaf
      (AlgebraicGeometry.AlgebraicSpaces.kernelPairToProduct B S' hS' φ').hom :=
    MorphismProperty.of_isPullback (P := P.presheaf)
      ((AlgebraicGeometry.AlgebraicSpaces.isPullback_kernelPairToProduct B S' hS' φ').map
        (ObjectProperty.ι _)) hsep
  -- the base changes of `p₀, p₁` are that kernel pair
  have h₁' : (ObjectProperty.homMk (prod.lift (bc.map p₀).hom (bc.map p₁).hom) :
      bc.obj W ⟶ AlgebraicGeometry.AlgebraicSpaces.product B S' hS' (bc.obj T) (bc.obj T)) =
      hk.isoPullback.hom ≫ AlgebraicGeometry.AlgebraicSpaces.kernelPairToProduct B S' hS' φ' := by
    refine AlgebraicGeometry.AlgebraicSpaces.product_hom_ext B S' hS' ?_ ?_
    · rw [Category.assoc, AlgebraicGeometry.AlgebraicSpaces.kernelPairToProduct_comp_fst,
        hk.isoPullback_hom_fst]
      exact ObjectProperty.hom_ext _ (prod.lift_fst _ _)
    · rw [Category.assoc, AlgebraicGeometry.AlgebraicSpaces.kernelPairToProduct_comp_snd,
        hk.isoPullback_hom_snd]
      exact ObjectProperty.hom_ext _ (prod.lift_snd _ _)
  have h₁ : prod.lift (bc.map p₀).hom (bc.map p₁).hom =
      ((ObjectProperty.ι _).mapIso hk.isoPullback).hom ≫
        (AlgebraicGeometry.AlgebraicSpaces.kernelPairToProduct B S' hS' φ').hom :=
    congrArg (fun z => z.hom) h₁'
  have hlift : P.presheaf (prod.lift (bc.map p₀).hom (bc.map p₁).hom) := by
    rw [h₁]
    exact MorphismProperty.RespectsIso.precomp P.presheaf _ _ hker
  -- base change commutes with the binary product
  let k := PreservesLimitPair.iso rR T.obj T.obj
  have h₂ : rR.map (prod.lift p₀.hom p₁.hom) ≫ k.hom =
      prod.lift (bc.map p₀).hom (bc.map p₁).hom := by
    apply prod.hom_ext
    · simp only [k, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_fst,
        prod.lift_fst, ← Functor.map_comp]
      exact (prod.lift_fst _ _).symm
    · simp only [k, Category.assoc, PreservesLimitPair.iso_hom, prodComparison_snd,
        prod.lift_snd, ← Functor.map_comp]
      exact (prod.lift_snd _ _).symm
  change P.presheaf (rR.map (prod.lift p₀.hom p₁.hom))
  rw [(Iso.eq_comp_inv k).mpr h₂]
  exact MorphismProperty.RespectsIso.postcomp P.presheaf k.inv _ hlift

end ClosedImmersion

/-! ### The realization, leg by leg -/

section Leg

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The quotient of one leg.** Let `π' : T' ⟶ Y'` coequalize `a, b : W' ⟶ T'` and be universal
among maps to algebraic spaces with that property, and let `a, b` be the kernel pair of a
locally surjective `φ' : T' ⟶ Z'`. Then `Y' ≅ Z'` by an isomorphism carrying `π'` to `φ'`. -/
theorem exists_iso_of_quotient_leg {W' T' Y' Z' : AlgebraicSpaces B S hS} (a b : W' ⟶ T')
    (π' : T' ⟶ Y') (φ' : T' ⟶ Z') (hπ : a ≫ π' = b ≫ π')
    (hu : ∀ (A : AlgebraicSpaces B S hS) (k : T' ⟶ A), a ≫ k = b ≫ k → ∃! d : Y' ⟶ A, π' ≫ d = k)
    (hk : IsPullback a b φ' φ')
    (hs : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ'.hom) :
    ∃ e : Y' ≅ Z', π' ≫ e.hom = φ' := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  obtain ⟨d, hd, -⟩ := hu Z' φ' hk.w
  obtain ⟨χ, hχ, -⟩ := AlgebraicGeometry.Space.existsUnique_desc_of_isLocallySurjective
    Z'.property.isSheaf (hk.map (ObjectProperty.ι _)) hs Y'.property.isSheaf π'.hom
    (congrArg (fun z => z.hom) hπ)
  let χ' : Z' ⟶ Y' := ObjectProperty.homMk χ
  have hχ' : φ' ≫ χ' = π' := ObjectProperty.hom_ext _ hχ
  have h₁ : d ≫ χ' = 𝟙 Y' := by
    obtain ⟨_, -, huniq⟩ := hu Y' π' hπ
    have e₁ : π' ≫ d ≫ χ' = π' := by rw [← Category.assoc, hd, hχ']
    exact (huniq _ e₁).trans (huniq _ (Category.comp_id _)).symm
  obtain ⟨_, -, hZu⟩ := AlgebraicGeometry.Space.existsUnique_desc_of_isLocallySurjective
    Z'.property.isSheaf (hk.map (ObjectProperty.ι _)) hs Z'.property.isSheaf φ'.hom
    (congrArg (fun z => z.hom) hk.w)
  have h₂ : χ' ≫ d = 𝟙 Z' := by
    apply ObjectProperty.hom_ext
    have e₁ : φ'.hom ≫ (χ' ≫ d).hom = φ'.hom :=
      congrArg (fun z => z.hom) (show φ' ≫ χ' ≫ d = φ' by rw [← Category.assoc, hχ', hd])
    have e₂ : φ'.hom ≫ 𝟙 Z'.obj = φ'.hom := Category.comp_id _
    exact (hZu _ e₁).trans (hZu _ e₂).symm
  exact ⟨⟨d, χ', h₁, h₂⟩, hd⟩

/-- A universal coequalizing map is an epimorphism onto algebraic spaces. -/
theorem cancel_of_quotient_leg {W' T' Y' : AlgebraicSpaces B S hS} (a b : W' ⟶ T')
    (π' : T' ⟶ Y') (hπ : a ≫ π' = b ≫ π')
    (hu : ∀ (A : AlgebraicSpaces B S hS) (k : T' ⟶ A), a ≫ k = b ≫ k → ∃! d : Y' ⟶ A, π' ≫ d = k)
    {A : AlgebraicSpaces B S hS} {x y : Y' ⟶ A} (hxy : π' ≫ x = π' ≫ y) : x = y := by
  obtain ⟨_, -, huniq⟩ := hu A (π' ≫ x) (by rw [← Category.assoc, hπ, Category.assoc])
  exact (huniq x rfl).trans (huniq y hxy.symm).symm

end Leg

/-! ### The realization -/

section Realization

variable (B : BigFppfSite.{u}) (U' U X' X : Scheme.{u}) (hU' : B.Contains U')
  (hU : B.Contains U) (hX' : B.Contains X') (hX : B.Contains X)
  (gU : B.obj hU' ⟶ B.obj hU) (gX' : B.obj hU' ⟶ B.obj hX')
  (jU : B.obj hU ⟶ B.obj hX) (jX' : B.obj hX' ⟶ B.obj hX)
  (hcomm : gU ≫ jU = gX' ≫ jX')
  (G : GlueingFunctorSpec B U' U X' X hU' hU hX' hX gU gX' jU jX' hcomm)

/-- An isomorphism to a component of a triple which carries the base change of `π` to the
corresponding component of `φ`, read through the gluing functor. -/
theorem overMap_comp_eq {C D E : Type*} [Category C] [Category D] [Category E] {Gf : C ⥤ D}
    {O : D ⥤ E} {Bc : C ⥤ E} (α : Gf ⋙ O ≅ Bc) {T Y : C} {Z : D} (π : T ⟶ Y)
    (φ : Gf.obj T ⟶ Z) (e : Bc.obj Y ≅ O.obj Z) (he : Bc.map π ≫ e.hom = α.inv.app T ≫ O.map φ) :
    O.map (Gf.map π) ≫ (α.app Y ≪≫ e).hom = O.map φ := by
  have n := α.hom.naturality π
  simp only [Functor.comp_map] at n
  rw [Iso.trans_hom, Iso.app_hom, ← Category.assoc, n, Category.assoc, he,
    Iso.hom_inv_id_app_assoc]

/-- Cancellation of `O.map (Gf.map π)` from a cancellation of `Bc.map π`. -/
theorem overMap_cancel {C D E : Type*} [Category C] [Category D] [Category E] {Gf : C ⥤ D}
    {O : D ⥤ E} {Bc : C ⥤ E} (α : Gf ⋙ O ≅ Bc) {T Y : C} (π : T ⟶ Y)
    (hc : ∀ {A : E} (x y : Bc.obj Y ⟶ A), Bc.map π ≫ x = Bc.map π ≫ y → x = y)
    {A : E} (x y : O.obj (Gf.obj Y) ⟶ A) (hxy : O.map (Gf.map π) ≫ x = O.map (Gf.map π) ≫ y) :
    x = y := by
  have n := α.inv.naturality π
  simp only [Functor.comp_map] at n
  have : Bc.map π ≫ (α.inv.app Y ≫ x) = Bc.map π ≫ (α.inv.app Y ≫ y) := by
    rw [← Category.assoc, n, Category.assoc, hxy, ← Category.assoc, ← n, Category.assoc]
  simpa using congrArg (α.hom.app Y ≫ ·) (hc _ _ this)

/-- If `fl` and `fr` carry `pl` and `pr` to `φl` and `φr`, both `φ` and `p` satisfy a structure
square for `F`, and `pl` is an epimorphism onto `F.obj Zr`, then `fl, fr` respect the squares. -/
private theorem comp_eq_of_structure_squares {C D : Type*} [Category C] [Category D] (F : D ⥤ C)
    {Tl Yl Zl : C} {Tr Yr Zr : D} {pl : Tl ⟶ Yl} {pr : Tr ⟶ Yr} {φl : Tl ⟶ Zl} {φr : Tr ⟶ Zr}
    {fl : Yl ⟶ Zl} {fr : Yr ⟶ Zr} {Th : Tl ⟶ F.obj Tr} {Yh : Yl ⟶ F.obj Yr}
    {Zh : Zl ⟶ F.obj Zr} (hl : pl ≫ fl = φl) (hr : pr ≫ fr = φr)
    (wφ : φl ≫ Zh = Th ≫ F.map φr) (wπ : pl ≫ Yh = Th ≫ F.map pr)
    (hc : ∀ x y : Yl ⟶ F.obj Zr, pl ≫ x = pl ≫ y → x = y) : fl ≫ Zh = Yh ≫ F.map fr := by
  apply hc
  rw [← Category.assoc, hl, wφ, ← Category.assoc, wπ, Category.assoc, ← Functor.map_comp, hr]

/-- **The realization step of Stacks 0F9U.** Let `φ : G(T) ⟶ Z` be a morphism of triples and
`π : T ⟶ Y` a morphism of algebraic spaces over `X` coequalizing `p₀, p₁ : W ⟶ T`. Suppose that
on each of the three legs the base change of `π` is universal among maps to algebraic spaces
coequalizing the base changes of `p₀, p₁`, and that the latter are the kernel pair of the
corresponding (locally surjective) component of `φ`. Then `G(Y) ≅ Z`. -/
theorem nonempty_glueingFunctor_iso_of_quotient {W T Y : AlgebraicSpaces B X hX}
    (p₀ p₁ : W ⟶ T) (π : T ⟶ Y) (hπ : p₀ ≫ π = p₁ ≫ π)
    {Z : GlueingData B U' U X' hU' hU hX' gU gX'} (φ : G.functor.obj T ⟶ Z)
    (huU : ∀ (A : AlgebraicSpaces B U hU) (k : (baseChange B U X hU hX jU).obj T ⟶ A),
      (baseChange B U X hU hX jU).map p₀ ≫ k = (baseChange B U X hU hX jU).map p₁ ≫ k →
        ∃! d, (baseChange B U X hU hX jU).map π ≫ d = k)
    (huM : ∀ (A : AlgebraicSpaces B U' hU')
      (k : (baseChange B U' X hU' hX (gU ≫ jU)).obj T ⟶ A),
      (baseChange B U' X hU' hX (gU ≫ jU)).map p₀ ≫ k =
          (baseChange B U' X hU' hX (gU ≫ jU)).map p₁ ≫ k →
        ∃! d, (baseChange B U' X hU' hX (gU ≫ jU)).map π ≫ d = k)
    (huX : ∀ (A : AlgebraicSpaces B X' hX') (k : (baseChange B X' X hX' hX jX').obj T ⟶ A),
      (baseChange B X' X hX' hX jX').map p₀ ≫ k = (baseChange B X' X hX' hX jX').map p₁ ≫ k →
        ∃! d, (baseChange B X' X hX' hX jX').map π ≫ d = k)
    (hkU : IsPullback ((baseChange B U X hU hX jU).map p₀) ((baseChange B U X hU hX jU).map p₁)
      (G.overUIso.inv.app T ≫ (overU B U' U X' hU' hU hX' gU gX').map φ)
      (G.overUIso.inv.app T ≫ (overU B U' U X' hU' hU hX' gU gX').map φ))
    (hkM : IsPullback ((baseChange B U' X hU' hX (gU ≫ jU)).map p₀)
      ((baseChange B U' X hU' hX (gU ≫ jU)).map p₁)
      (G.overU'Iso.inv.app T ≫ (overU' B U' U X' hU' hU hX' gU gX').map φ)
      (G.overU'Iso.inv.app T ≫ (overU' B U' U X' hU' hU hX' gU gX').map φ))
    (hkX : IsPullback ((baseChange B X' X hX' hX jX').map p₀)
      ((baseChange B X' X hX' hX jX').map p₁)
      (G.overX'Iso.inv.app T ≫ (overX' B U' U X' hU' hU hX' gU gX').map φ)
      (G.overX'Iso.inv.app T ≫ (overX' B U' U X' hU' hU hX' gU gX').map φ))
    (hsU : Presheaf.IsLocallySurjective (BigFppfOver.topology B U hU)
      (G.overUIso.inv.app T ≫ (overU B U' U X' hU' hU hX' gU gX').map φ).hom)
    (hsM : Presheaf.IsLocallySurjective (BigFppfOver.topology B U' hU')
      (G.overU'Iso.inv.app T ≫ (overU' B U' U X' hU' hU hX' gU gX').map φ).hom)
    (hsX : Presheaf.IsLocallySurjective (BigFppfOver.topology B X' hX')
      (G.overX'Iso.inv.app T ≫ (overX' B U' U X' hU' hU hX' gU gX').map φ).hom) :
    Nonempty (G.functor.obj Y ≅ Z) := by
  have hπU := (baseChange B U X hU hX jU).congr_map hπ
  have hπM := (baseChange B U' X hU' hX (gU ≫ jU)).congr_map hπ
  have hπX := (baseChange B X' X hX' hX jX').congr_map hπ
  simp only [Functor.map_comp] at hπU hπM hπX
  obtain ⟨eU, heU⟩ := exists_iso_of_quotient_leg _ _ _ _ hπU huU hkU hsU
  obtain ⟨eM, heM⟩ := exists_iso_of_quotient_leg _ _ _ _ hπM huM hkM hsM
  obtain ⟨eX, heX⟩ := exists_iso_of_quotient_leg _ _ _ _ hπX huX hkX hsX
  obtain ⟨fU, hfU⟩ : ∃ f : (overU B U' U X' hU' hU hX' gU gX').obj (G.functor.obj Y) ≅
      (overU B U' U X' hU' hU hX' gU gX').obj Z,
      (G.functor.map π).hom.left.right ≫ f.hom = φ.hom.left.right :=
    ⟨_, overMap_comp_eq G.overUIso π φ eU heU⟩
  obtain ⟨fM, hfM⟩ : ∃ f : (overU' B U' U X' hU' hU hX' gU gX').obj (G.functor.obj Y) ≅
      (overU' B U' U X' hU' hU hX' gU gX').obj Z,
      (G.functor.map π).hom.left.left ≫ f.hom = φ.hom.left.left :=
    ⟨_, overMap_comp_eq G.overU'Iso π φ eM heM⟩
  obtain ⟨fX, hfX⟩ : ∃ f : (overX' B U' U X' hU' hU hX' gU gX').obj (G.functor.obj Y) ≅
      (overX' B U' U X' hU' hU hX' gU gX').obj Z,
      (G.functor.map π).hom.right ≫ f.hom = φ.hom.right :=
    ⟨_, overMap_comp_eq G.overX'Iso π φ eX heX⟩
  have cM : ∀ {A : AlgebraicSpaces B U' hU'}
      (x y : (overU' B U' U X' hU' hU hX' gU gX').obj (G.functor.obj Y) ⟶ A),
      (overU' B U' U X' hU' hU hX' gU gX').map (G.functor.map π) ≫ x =
        (overU' B U' U X' hU' hU hX' gU gX').map (G.functor.map π) ≫ y → x = y :=
    fun x y h => overMap_cancel G.overU'Iso π
      (fun x y hxy => cancel_of_quotient_leg _ _ _ hπM huM hxy) x y h
  -- the two structure squares of `φ` and of `G(π)`
  have wφU := φ.hom.left.w
  have wφX := φ.hom.w
  have wπU := (G.functor.map π).hom.left.w
  have wπX := (G.functor.map π).hom.w
  dsimp only [Functor.id_obj, Functor.id_map, Comma.fst_obj, Comma.fst_map] at wφU wφX wπU wπX
  exact ⟨glueingDataIsoOfComponents B U' U X' hU' hU hX' gU gX' fM fU fX
    (comp_eq_of_structure_squares _ hfM hfU wφU wπU cM)
    (comp_eq_of_structure_squares _ hfM hfX wφX wπX cM)⟩

end Realization

end BeauvilleLaszlo.Space

end
