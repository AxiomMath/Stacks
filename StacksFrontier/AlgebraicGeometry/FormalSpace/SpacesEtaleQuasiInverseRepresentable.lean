module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableSource
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticTransfer
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleQuasiInverseBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleEssSurj
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleRangeEquivalence
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentificationSupplement
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SetTheoreticDescentRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# `U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale

Let `S` be a scheme contained in a big fppf site `B`. This file proves the verification the
source of Stacks 0DEG omits: the structure morphism `U_{V, ψ} ⟶ X` of the quasi-inverse
`AlgebraicGeometry.FormalSpace.liftAlong` is representable by algebraic spaces and étale, as
soon as `i : I ⟶ X` is a representable thickening injective on sections — the inclusion of a
reduction is one — and `p : W ⟶ I` is itself representable by algebraic spaces and étale.

## Main definitions

* `AlgebraicGeometry.FormalSpace.liftAlongMk`: the morphism `Z ⟶ U_{V, ψ}` over `X` attached
  to an identification of `Z ×_X I` with `W` over `I`. This is the half of the universal
  property of the dependent product that produces morphisms into it.

## Main results

* `AlgebraicGeometry.FormalSpace.liftAlong_hom_ext`: a morphism `Z ⟶ U_{V, ψ}` over `X` is
  determined by the morphism `Z ×_X I ⟶ W` it induces. This is the uniqueness half of the
  universal property of the dependent product, in the form in which it is used.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftSheafMap`: the universe lift of an
  étale morphism of algebraic spaces is representable by algebraic spaces and étale.
* `AlgebraicGeometry.FormalSpace.exists_iso_liftAlong_of_isThickening`: the dependent product of
  an algebraic space étale over an object `T` of the site along a thickening `T₀ ⟶ T` of that
  object is the algebraic space itself. This is the geometric heart, and it is the
  general-thickening case of Stacks 05ZH.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongBase` and
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_spacesEtaleQuasiInverseBase`:
  **Stacks 0DEG**, the omitted verification that `U_{V, ψ} ⟶ X` is representable by algebraic
  spaces and étale.
* `AlgebraicGeometry.FormalSpace.isRepresentableEtale_liftAlongMap`: the quasi-inverse on
  morphisms is representable by algebraic spaces and étale as soon as the morphism it transports
  is. This is the step at which an atlas of `U_{V, ψ}` built out of charts of `V` gets its
  structure morphisms, and it needs no factorization of a scheme-valued point of `U_{V, ψ}`
  through a stage of a presentation: the dependent product computes that base change outright.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_affine`: the reduction the
  source performs, from a general base to an affine formal algebraic chart of it.
* `FormalSpace.essSurj_spacesEtaleComparison_of_isFormalAlgebraicSpace_quasiInverse` and
  `AlgebraicGeometry.FormalSpace.essSurj_spacesEtaleComparison_of_affine`: essential
  surjectivity of the comparison functor of Stacks 0DEG, reduced first to the single assertion
  that `U_{V, ψ}` is a formal algebraic space and then to the affine case of that assertion.
  The affine case is proved in
  `StacksFrontier/AlgebraicGeometry/FormalSpace/LiftAlongAffineBase.lean`, so essential
  surjectivity itself is unconditional:
  `AlgebraicGeometry.FormalSpace.essSurj_spacesEtaleComparison`.

## Implementation notes

The two halves of the universal property of the dependent product are proved on sections, with
the cartesianness of the square identifying `Z ×_X I` with `W` consumed in the sectionwise form
`AlgebraicGeometry.FormalSpace.IsSectionwisePullback` of
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverseBaseChange.lean`, whose
`AlgebraicGeometry.FormalSpace.bcPoint` is reused here as the chosen section of `W` above a
compatible pair.

## References

* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Morphisms into the dependent product -/

section Mk

variable {B S hS} {X I W Z : FppfSheaf B S hS} {i : I ⟶ X} {p : W ⟶ I} {ζ : Z ⟶ X}
  {c₀ : W ⟶ Z} (hex : IsSectionwisePullback B S hS c₀ p ζ i)

end Mk

/-! ### Morphisms into the dependent product are determined on the fibre product -/

section HomExt

variable {B S hS} {X I W Z : FppfSheaf B S hS} {i : I ⟶ X} {p : W ⟶ I}

end HomExt

/-! ### The universe lift of an étale morphism of algebraic spaces -/

/-- **The universe lift of an étale morphism of algebraic spaces over `S` is representable by
algebraic spaces and étale.** Representability is the fibre product of algebraic spaces,
Stacks 02X2, and étaleness of the base changes is Stacks 0466 read through the universe lift. -/
theorem isRepresentableEtale_liftSheafMap {A A' : AlgebraicSpaces B S hS} (a : A ⟶ A')
    (ha : Space.IsEtale B S hS a.hom) :
    IsRepresentableEtale B S hS (liftSheafMap B S hS a) := by
  have hrep : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS
      (liftSheafMap B S hS a).hom :=
    (Space.isRepresentableByAlgebraicSpacesULift_whiskerRight_iff B S hS a.hom).mpr
      (fun U ξ ↦ isAlgebraicSpace_pullback B S hS ξ a.hom
        (isAlgebraicSpace_yoneda B S hS U) A.property A'.property)
  exact ⟨hrep, hasPropertyULift_whiskerRight_of_isEtale B S hS A.property A'.property
    a.hom ha hrep⟩

/-! ### The dependent product along a thickening of schemes of the site -/

section SiteThickening

variable {B S hS}

/-- An endomorphism of the dependent product `U_{W, p}` over `X` which fixes the canonical
section `W ⟶ U_{W, p}` is the identity. -/
theorem liftAlong_eq_id_of_liftAlongSection_comp {X I W : FppfSheaf B S hS} {i : I ⟶ X}
    {p : W ⟶ I}
    (hinj : ∀ T : BigFppfOver B S hS, Function.Injective (i.hom.app (Opposite.op T)))
    {f : liftAlong B S hS i p ⟶ liftAlong B S hS i p}
    (hf : f ≫ liftAlongBase B S hS i p = liftAlongBase B S hS i p)
    (hfs : liftAlongSection B S hS hinj ≫ f = liftAlongSection B S hS hinj) :
    f = 𝟙 _ := by
  have hLS := isSectionwisePullback_of_isPullback B S hS
    (isPullback_liftAlongSection B S hS hinj (i := i) (p := p))
  refine liftAlong_hom_ext (by rw [hf, Category.id_comp]) fun T' ζ w h h' ↦ ?_
  have hζb : (liftAlongBase B S hS i p).hom.app (Opposite.op T') ζ
      = i.hom.app (Opposite.op T') w := by
    refine Eq.trans ?_ h'.symm
    exact (Functor.map_id_apply X.obj _ _).symm
  obtain ⟨y, ⟨hy, -⟩, -⟩ := hLS T' ζ w hζb
  have hfix : f.hom.app (Opposite.op T') ζ = ζ := by
    rw [← hy]
    exact congrArg (fun m : W ⟶ liftAlong B S hS i p ↦ m.hom.app (Opposite.op T') y) hfs
  exact LiftAlong.lift_congr hfix rfl rfl h h'

/-- **The dependent product of an algebraic space étale over an object `T` of the site along a
thickening `T₀ ⟶ T` of that object is the algebraic space itself.** Let `a : A₀ ⟶ T` be an
étale morphism of algebraic spaces over `S` and let `W` be its base change along a thickening
`T₀ ⟶ T` of objects of the site. Then the comparison morphism `A₀ ⟶ U_{W, p}` of
`AlgebraicGeometry.FormalSpace.liftAlongMk` is an isomorphism over `T`.

This is the geometric content of the verification Stacks 0DEG omits. The comparison morphism is
an isomorphism because a section of `A₀` over an object `T'` of the site is the same thing as a
section of its base change to `T' ×_T T₀`, which is the general-thickening case of Stacks 05ZH
in the form `AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening`: the
inverse is the unique extension of the projection `W ⟶ A₀` along the representable thickening
`W ⟶ U_{W, p}`, and the two composites are identified by the uniqueness halves of that
statement and of the universal property of the dependent product. -/
theorem exists_iso_liftAlong_of_isThickening
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {A₀ : AlgebraicSpaces B S hS} {a : A₀ ⟶ schemeSpace T}
    (ha : Space.IsEtale B S hS a.hom)
    {W : FppfSheaf B S hS} {p : W ⟶ liftSheaf B S hS (schemeSpace T₀)}
    {c₀ : W ⟶ liftSheaf B S hS A₀}
    (hfin : IsPullback c₀.hom p.hom (liftSheafMap B S hS a).hom
      (liftSheafMap B S hS (schemeSpaceMap k)).hom) :
    ∃ e : liftSheaf B S hS A₀
        ≅ liftAlong B S hS (liftSheafMap B S hS (schemeSpaceMap k)) p,
      e.hom ≫ liftAlongBase B S hS (liftSheafMap B S hS (schemeSpaceMap k)) p
        = liftSheafMap B S hS a := by
  set i' : liftSheaf B S hS (schemeSpace T₀) ⟶ liftSheaf B S hS (schemeSpace T) :=
    liftSheafMap B S hS (schemeSpaceMap k) with hi'
  -- the thickening, read as a representable thickening of fppf sheaves
  have hthick : Space.IsRepresentableThickeningULift.{u + 1} B S hS i'.hom :=
    MorphismProperty.relative_map hk
  have hinj : ∀ T' : BigFppfOver B S hS,
      Function.Injective (i'.hom.app (Opposite.op T')) := fun T' ↦
    (mono_iff_injective _).1 ((NatTrans.mono_iff_mono_app _).1
      (mono_of_isRepresentableThickeningULift B S hS hthick) (Opposite.op T'))
  have hex := isSectionwisePullback_of_isPullback_hom B S hS hfin
  have hw : c₀ ≫ liftSheafMap B S hS a = p ≫ i' := Sheaf.hom_ext hfin.w
  -- the comparison morphism and the two identities it satisfies
  set c : liftSheaf B S hS A₀ ⟶ liftAlong B S hS i' p := liftAlongMk hex with hc
  have hcbase : c ≫ liftAlongBase B S hS i' p = liftSheafMap B S hS a :=
    liftAlongMk_comp_liftAlongBase hex
  have hcc₀ : c₀ ≫ c = liftAlongSection B S hS hinj := comp_liftAlongMk hex hw hinj
  -- `W ⟶ U_{W, p}` and `W ⟶ A₀` are representable thickenings, being base changes of `i'`
  have hsec := isPullback_liftAlongSection B S hS hinj (i := i') (p := p)
  have hthickS : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (liftAlongSection B S hS hinj (i := i') (p := p)).hom :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hsec.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hthick
  have hthickC : Space.IsRepresentableThickeningULift.{u + 1} B S hS c₀.hom :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback hfin.flip hthick
  have hae : IsRepresentableEtale B S hS (liftSheafMap B S hS a) :=
    isRepresentableEtale_liftSheafMap B S hS a ha
  -- the inverse: the unique extension of `W ⟶ A₀` along the thickening `W ⟶ U_{W, p}`
  obtain ⟨d, ⟨hd₁, hd₂⟩, -⟩ :=
    existsUnique_hom_of_isRepresentableThickening hthickS hae (liftAlongBase B S hS i' p)
      (show c₀ ≫ liftSheafMap B S hS a
        = liftAlongSection B S hS hinj ≫ liftAlongBase B S hS i' p from
        hw.trans (liftAlongSection_comp_liftAlongBase B S hS hinj).symm)
  -- `c ≫ d = 𝟙`, by the uniqueness of extensions along the thickening `W ⟶ A₀`
  have hcd : c ≫ d = 𝟙 (liftSheaf B S hS A₀) := by
    obtain ⟨g₀, -, hu⟩ :=
      existsUnique_hom_of_isRepresentableThickening hthickC hae (liftSheafMap B S hS a)
        rfl
    refine (hu (c ≫ d) ⟨?_, ?_⟩).trans (hu (𝟙 _) ⟨Category.id_comp _, Category.comp_id _⟩).symm
    · rw [Category.assoc, hd₁, hcbase]
    · rw [← Category.assoc, hcc₀, hd₂]
  -- `d ≫ c = 𝟙`, since a section of `U_{W, p}` carrying a section of `T₀` comes from `W`
  have hdc : d ≫ c = 𝟙 (liftAlong B S hS i' p) :=
    liftAlong_eq_id_of_liftAlongSection_comp hinj (by rw [Category.assoc, hcbase, hd₁])
      (by rw [← Category.assoc, hd₂, hcc₀])
  exact ⟨{ hom := c, inv := d, hom_inv_id := hcd, inv_hom_id := hdc }, hcbase⟩

/-- A morphism representable by algebraic spaces and étale from an fppf sheaf to an object `T₀`
of the site is, up to isomorphism of its source, the universe lift of an étale morphism from an
algebraic space in the value universe of the schemes. -/
theorem exists_isEtale_of_isRepresentableEtale {T₀ : BigFppfOver B S hS}
    {W : FppfSheaf B S hS} (p : W ⟶ liftSheaf B S hS (schemeSpace T₀))
    (hp : IsRepresentableEtale B S hS p) :
    ∃ (W₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS W₀)
      (eW : W₀ ⋙ uliftFunctor.{u + 1} ≅ W.obj) (p₀ : W₀ ⟶ yoneda.obj T₀),
      Space.IsEtale B S hS p₀ ∧ Functor.whiskerRight p₀ uliftFunctor.{u + 1} = eW.hom ≫ p.hom := by
  classical
  set H := (Functor.whiskeringRight ((BigFppfOver B S hS)ᵒᵖ) (Type u)
    (Type (u + 1))).obj uliftFunctor.{u + 1} with hH
  have hid : IsPullback p.hom (𝟙 W.obj)
      (𝟙 ((liftSheaf B S hS (schemeSpace T₀)).obj)) p.hom :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hWalg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS W.obj :=
    Space.isAlgebraicSpaceULift_of_iso B S hS hid.isoPullback.symm
      (hp.1 T₀ (𝟙 ((uliftYoneda.{u + 1}).obj T₀)))
  have hpet : Space.IsEtaleULift.{u + 1} B S hS p.hom := by
    have h1 := hp.2 T₀ (𝟙 ((uliftYoneda.{u + 1}).obj T₀))
    have h2 : hid.isoPullback.hom
        ≫ pullback.fst (𝟙 ((uliftYoneda.{u + 1}).obj T₀)) p.hom = p.hom :=
      hid.isoPullback_hom_fst
    rw [← h2]
    exact (Space.isEtaleULift_isIso_comp_iff B S hS hid.isoPullback.hom _).mpr h1
  obtain ⟨W₀, hW₀, ⟨eW⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS hWalg
  set p₀ : W₀ ⟶ yoneda.obj T₀ := (liftFullyFaithful B S hS).preimage (eW.hom ≫ p.hom) with hp₀d
  have hp₀ : H.map p₀ = eW.hom ≫ p.hom := (liftFullyFaithful B S hS).map_preimage _
  refine ⟨W₀, hW₀, eW, p₀, ?_, hp₀⟩
  refine (Space.isEtaleULift_whiskerRight_iff B S hS p₀).mp ?_
  show Space.IsEtaleULift.{u + 1} B S hS (H.map p₀)
  rw [hp₀]
  exact (Space.isEtaleULift_isIso_comp_iff B S hS eW.hom p.hom).mpr hpet

/-- **A morphism representable by algebraic spaces and étale over a thickening of an object of
the site extends to one over that object.** This is Stacks 05ZH at a thickening of schemes of
the site, read in the value universe of the formal algebraic spaces: the source of `p` is an
algebraic space, étale over the thin end `T₀`, and
`AlgebraicGeometry.Space.essSurj_spacesBaseChange_of_isThickening` lifts it to an algebraic
space étale over `T`, with the cartesian square identifying its base change with `p`. -/
theorem exists_isPullback_etaleLift_of_isThickening
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {W : FppfSheaf B S hS} (p : W ⟶ liftSheaf B S hS (schemeSpace T₀))
    (hp : IsRepresentableEtale B S hS p) :
    ∃ (A₀ : AlgebraicSpaces B S hS) (a : A₀ ⟶ schemeSpace T)
      (_ : Space.IsEtale B S hS a.hom) (c₀ : W ⟶ liftSheaf B S hS A₀),
      IsPullback c₀.hom p.hom (liftSheafMap B S hS a).hom
        (liftSheafMap B S hS (schemeSpaceMap k)).hom := by
  classical
  set H := (Functor.whiskeringRight ((BigFppfOver B S hS)ᵒᵖ) (Type u)
    (Type (u + 1))).obj uliftFunctor.{u + 1} with hH
  obtain ⟨W₀, hW₀, eW, p₀, hp₀et, hp₀⟩ := exists_isEtale_of_isRepresentableEtale p hp
  -- the étale lift across the thickening
  set fk : schemeSpace T₀ ⟶ schemeSpace T := schemeSpaceMap k with hfk
  have hthk := isThickeningHom_yonedaSpace_map B S hS k hk
  have : Mono fk.hom := hthk.mono
  have hess := (Space.isEquivalence_spacesBaseChange_of_isThickening_range B S hS fk
    hthk.2).essSurj
  set C : Space.SpacesEtale B S hS (schemeSpace T₀) :=
    ⟨Over.mk (ObjectProperty.homMk p₀ :
      (⟨W₀, hW₀⟩ : AlgebraicSpaces B S hS) ⟶ schemeSpace T₀), hp₀et⟩ with hC
  set A := (Space.spacesBaseChange B S hS fk).functor.objPreimage C with hA
  set eA := (Space.spacesBaseChange B S hS fk).functor.objObjPreimageIso C with heA
  set P := (Space.spacesBaseChange B S hS fk).functor.obj A with hP
  have hsqA := (Space.spacesBaseChange B S hS fk).isPullback A
  -- the comparison of the underlying presheaves
  set eP : P.obj.left.obj ≅ W₀ :=
    { hom := eA.hom.hom.left.hom
      inv := eA.inv.hom.left.hom
      hom_inv_id := congrArg (fun m : P ⟶ P ↦ m.hom.left.hom) eA.hom_inv_id
      inv_hom_id := congrArg (fun m : C ⟶ C ↦ m.hom.left.hom) eA.inv_hom_id } with heP
  have hPhom : eP.hom ≫ p₀ = P.obj.hom.hom :=
    congrArg (fun m : P.obj.left ⟶ schemeSpace T₀ ↦ m.hom) (Over.w eA.hom.hom)
  set δ : H.obj P.obj.left.obj ≅ W.obj := H.mapIso eP ≪≫ eW with hδd
  have hδ : δ.hom ≫ p.hom = H.map P.obj.hom.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ H.map eP.hom ≫ m) hp₀.symm).trans
        ((H.map_comp eP.hom p₀).symm.trans (congrArg H.map hPhom)))
  have hcancel : δ.inv ≫ H.map P.obj.hom.hom = p.hom :=
    (congrArg (fun m ↦ δ.inv ≫ m) hδ.symm).trans
      ((Category.assoc δ.inv δ.hom p.hom).symm.trans
        ((congrArg (fun m ↦ m ≫ p.hom) δ.inv_hom_id).trans (Category.id_comp p.hom)))
  have hpsq := (AlgebraicSpaces.isPullback_hom B S hS hsqA).map H
  refine ⟨A.obj.left, A.obj.hom, A.property,
    ⟨δ.inv ≫ H.map ((Space.spacesBaseChange B S hS fk).projection.app A).hom⟩, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (δ.symm ≪≫ hpsq.isoPullback) ?_ ?_
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ δ.inv ≫ m) hpsq.w).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun m ↦ m ≫ H.map fk.hom) hcancel)))
  · exact (Category.assoc _ _ _).trans
      (congrArg (fun m ↦ δ.inv ≫ m) hpsq.isoPullback_hom_fst)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun m ↦ δ.inv ≫ m) hpsq.isoPullback_hom_snd).trans hcancel)

/-- **The dependent product of a representable étale morphism along a thickening of schemes of
the site is an algebraic space, étale over the thick end.** This is the case of the verification
Stacks 0DEG omits to which the general case reduces by base change. -/
theorem isAlgebraicSpaceULift_isEtaleULift_liftAlong_of_isThickening
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {W : FppfSheaf B S hS} (p : W ⟶ liftSheaf B S hS (schemeSpace T₀))
    (hp : IsRepresentableEtale B S hS p) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS
        (liftAlong B S hS (liftSheafMap B S hS (schemeSpaceMap k)) p).obj ∧
      Space.IsEtaleULift.{u + 1} B S hS
        (liftAlongBase B S hS (liftSheafMap B S hS (schemeSpaceMap k)) p).hom := by
  obtain ⟨A₀, a, ha, c₀, hfin⟩ := exists_isPullback_etaleLift_of_isThickening k hk p hp
  obtain ⟨e, he⟩ := exists_iso_liftAlong_of_isThickening k hk ha hfin
  refine ⟨Space.isAlgebraicSpaceULift_of_iso B S hS
    ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso e)
    ((Space.isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS A₀.obj).mpr A₀.property), ?_⟩
  have : IsIso e.inv.hom :=
    ⟨e.hom.hom, congrArg (fun m ↦ m.hom) e.inv_hom_id, congrArg (fun m ↦ m.hom) e.hom_inv_id⟩
  rw [← e.inv_hom_id_assoc (liftAlongBase B S hS _ p), he]
  exact (Space.isEtaleULift_isIso_comp_iff B S hS e.inv.hom (liftSheafMap B S hS a).hom).mpr
    ((Space.isEtaleULift_whiskerRight_iff B S hS a.hom).mpr ha)

end SiteThickening

/-! ### Stacks 0DEG: `U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale -/

/-- A pullback square of presheaves whose cone point is an algebraic space and whose projection
to the base change is étale exhibits the pullback as an algebraic space with étale projection. -/
private theorem isAlgebraicSpaceULift_isEtaleULift_pullback_of_isPullback
    {P T' A X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} {ξ : T' ⟶ X} {g : A ⟶ X} {b : P ⟶ T'}
    {s : P ⟶ A} (h : IsPullback b s ξ g) (halg : Space.IsAlgebraicSpaceULift.{u + 1} B S hS P)
    (het : Space.IsEtaleULift.{u + 1} B S hS b) :
    Space.IsAlgebraicSpaceULift.{u + 1} B S hS (pullback ξ g) ∧
      Space.IsEtaleULift.{u + 1} B S hS (pullback.fst ξ g) := by
  refine ⟨Space.isAlgebraicSpaceULift_of_iso B S hS h.isoPullback halg, ?_⟩
  rw [← h.isoPullback_inv_fst]
  exact (Space.isEtaleULift_isIso_comp_iff B S hS h.isoPullback.inv _).mpr het

/-- **The structure morphism of the dependent product is representable by algebraic spaces and
étale.** Let `i : I ⟶ X` be a representable thickening of fppf sheaves over `S` — the inclusion
of a reduction is one — and let `p : W ⟶ I` be representable by algebraic spaces and étale. Then
`U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale.

The base change of `U_{V, ψ}` along a scheme-valued point `ξ : T ⟶ X` is, by the Beck–Chevalley
isomorphism `AlgebraicGeometry.FormalSpace.isPullback_liftAlongBaseChange`, the dependent
product of the base change of `p` along the thickening `T ×_{ξ, X} I ⟶ T` of schemes of the
site that the representability of `i` provides; and that dependent product is an algebraic space
étale over `T` by
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_isEtaleULift_liftAlong_of_isThickening`. -/
theorem isRepresentableEtale_liftAlongBase {X I W : FppfSheaf B S hS} {i : I ⟶ X} {p : W ⟶ I}
    (hirep : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    (hp : IsRepresentableEtale B S hS p) :
    IsRepresentableEtale B S hS (liftAlongBase B S hS i p) := by
  classical
  have key : ∀ (T : BigFppfOver B S hS) (ξ : (uliftYoneda.{u + 1}).obj T ⟶ X.obj),
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS
          (pullback ξ (liftAlongBase B S hS i p).hom) ∧
        Space.IsEtaleULift.{u + 1} B S hS
          (pullback.fst ξ (liftAlongBase B S hS i p).hom) := by
    intro T ξ
    have hk : Stacks.Thickenings.IsThickening
        ((BigFppfOver.toScheme B S hS).map (hirep.rep.snd ξ)) := hirep.property_snd ξ
    set f' : liftSheaf B S hS (schemeSpace T) ⟶ X := ⟨ξ⟩ with hf'
    set g' : liftSheaf B S hS (schemeSpace (hirep.rep.pullback ξ)) ⟶ I :=
      ⟨hirep.rep.fst ξ⟩ with hg'
    have hIex : IsSectionwisePullback B S hS
        (liftSheafMap B S hS (schemeSpaceMap (hirep.rep.snd ξ))) g' f' i :=
      isSectionwisePullback_of_isPullback_hom B S hS (hirep.rep.isPullback ξ).flip
    have hWex : IsSectionwisePullback B S hS (pullback.snd p g') (pullback.fst p g') g' p :=
      isSectionwisePullback_of_isPullback B S hS (IsPullback.of_hasPullback p g').flip
    have hcomm : liftSheafMap B S hS (schemeSpaceMap (hirep.rep.snd ξ)) ≫ f' = g' ≫ i :=
      Sheaf.hom_ext (hirep.rep.isPullback ξ).flip.w
    have hcomm' : pullback.fst p g' ≫ p = pullback.snd p g' ≫ g' := pullback.condition
    have hp' : IsRepresentableEtale B S hS (pullback.snd p g') :=
      isRepresentableEtale_pullback_snd B S hS p g' hp
    obtain ⟨halg, het⟩ :=
      isAlgebraicSpaceULift_isEtaleULift_liftAlong_of_isThickening (hirep.rep.snd ξ) hk
        (pullback.snd p g') hp'
    have hbcP := (isPullback_liftAlongBaseChange (pullback.fst p g') hIex hWex hcomm
      hcomm').flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    exact isAlgebraicSpaceULift_isEtaleULift_pullback_of_isPullback B S hS hbcP halg het
  exact ⟨fun T ξ ↦ (key T ξ).1, fun T ξ ↦ (key T ξ).2⟩

/-- **The quasi-inverse on morphisms is representable by algebraic spaces and étale as soon as
the morphism it transports is.** Let `i : I ⟶ X` be a representable thickening of fppf sheaves
over `S` and let `k : W ⟶ Wt` be a morphism over `I` which is representable by algebraic spaces
and étale. Then `U_{W, p} ⟶ U_{Wt, pt}` is representable by algebraic spaces and étale.

This needs no factorization of a scheme-valued point of `U_{Wt, pt}` through anything: by
`AlgebraicGeometry.FormalSpace.isPullback_liftAlongMap`, the base change of `U_{W, p}` along a
point `T ⟶ U_{Wt, pt}` is the dependent product, along the thickening `T₀ ⟶ T` of schemes of
the site that the representability of `i` provides, of the base change of `k` along the
morphism `T₀ ⟶ Wt` that the point determines; and that dependent product is an algebraic space
étale over `T` by
`AlgebraicGeometry.FormalSpace.isAlgebraicSpaceULift_isEtaleULift_liftAlong_of_isThickening`. -/
theorem isRepresentableEtale_liftAlongMap {X I W Wt : FppfSheaf B S hS} {i : I ⟶ X}
    {p : W ⟶ I} {pt : Wt ⟶ I} (k : W ⟶ Wt) (hk : k ≫ pt = p)
    (hirep : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    (hkrep : IsRepresentableEtale B S hS k) :
    IsRepresentableEtale B S hS (liftAlongMap B S hS i k hk) := by
  classical
  have key : ∀ (T : BigFppfOver B S hS)
      (ξ : (uliftYoneda.{u + 1}).obj T ⟶ (liftAlong B S hS i pt).obj),
      Space.IsAlgebraicSpaceULift.{u + 1} B S hS
          (pullback ξ (liftAlongMap B S hS i k hk).hom) ∧
        Space.IsEtaleULift.{u + 1} B S hS
          (pullback.fst ξ (liftAlongMap B S hS i k hk).hom) := by
    intro T ξ
    set σ : liftSheaf B S hS (schemeSpace T) ⟶ liftAlong B S hS i pt := ⟨ξ⟩ with hσd
    set f' : liftSheaf B S hS (schemeSpace T) ⟶ X :=
      ⟨ξ ≫ (liftAlongBase B S hS i pt).hom⟩ with hf'
    have hσ : σ ≫ liftAlongBase B S hS i pt = f' := Sheaf.hom_ext rfl
    have hthk : Stacks.Thickenings.IsThickening
        ((BigFppfOver.toScheme B S hS).map (hirep.rep.snd f'.hom)) := hirep.property_snd f'.hom
    set g' : liftSheaf B S hS (schemeSpace (hirep.rep.pullback f'.hom)) ⟶ I :=
      ⟨hirep.rep.fst f'.hom⟩ with hg'
    have hIex : IsSectionwisePullback B S hS
        (liftSheafMap B S hS (schemeSpaceMap (hirep.rep.snd f'.hom))) g' f' i :=
      isSectionwisePullback_of_isPullback_hom B S hS (hirep.rep.isPullback f'.hom).flip
    have hcomm : liftSheafMap B S hS (schemeSpaceMap (hirep.rep.snd f'.hom)) ≫ f' = g' ≫ i :=
      Sheaf.hom_ext (hirep.rep.isPullback f'.hom).flip.w
    have hWex : IsSectionwisePullback B S hS (pullback.fst k (bcPointSection hσ hcomm))
        (pullback.snd k (bcPointSection hσ hcomm)) k (bcPointSection hσ hcomm) :=
      isSectionwisePullback_of_isPullback B S hS
        (IsPullback.of_hasPullback k (bcPointSection hσ hcomm))
    have hcommW : pullback.fst k (bcPointSection hσ hcomm) ≫ k
        = pullback.snd k (bcPointSection hσ hcomm) ≫ bcPointSection hσ hcomm :=
      pullback.condition
    have hcomm' : pullback.fst k (bcPointSection hσ hcomm) ≫ p
        = pullback.snd k (bcPointSection hσ hcomm) ≫ g' := by
      rw [← hk, ← Category.assoc, hcommW, Category.assoc,
        bcPointSection_comp_proj hσ hcomm]
    have hp' : IsRepresentableEtale B S hS (pullback.snd k (bcPointSection hσ hcomm)) :=
      isRepresentableEtale_pullback_snd B S hS k (bcPointSection hσ hcomm) hkrep
    obtain ⟨halg, het⟩ :=
      isAlgebraicSpaceULift_isEtaleULift_liftAlong_of_isThickening (hirep.rep.snd f'.hom) hthk
        (pullback.snd k (bcPointSection hσ hcomm)) hp'
    have hbcP := (isPullback_liftAlongMap (pullback.fst k (bcPointSection hσ hcomm)) hIex hk hσ
      hcomm hWex hcommW hcomm').flip.map
        (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))
    exact isAlgebraicSpaceULift_isEtaleULift_pullback_of_isPullback B S hS hbcP halg het
  exact ⟨fun T ξ ↦ (key T ξ).1, fun T ξ ↦ (key T ξ).2⟩

/-- **Stacks 0DEG.** The structure morphism `U_{V, ψ} ⟶ X` of the quasi-inverse of the proof is
representable by algebraic spaces and étale. This is one of the two verifications the source
omits — "we omit the verification that `U_{V, ψ} ⟶ X` is representable by algebraic spaces and
étale" — and it is proved here outright. -/
@[stacks 0DEG "the omitted verification that `U_{V, ψ} ⟶ X` is representable by algebraic \
spaces and étale"]
theorem isRepresentableEtale_spacesEtaleQuasiInverseBase {X : FppfSheaf B S hS}
    (R : Reduction B S hS X) (V : R.SpacesEtale) :
    IsRepresentableEtale B S hS (spacesEtaleQuasiInverseBase B S hS R V) :=
  isRepresentableEtale_liftAlongBase B S hS R.isReduction.isRepresentableThickening
    (isRepresentableEtale_liftSheafMap B S hS V.obj.hom V.property)

/-! ### Reduction of the dependent product to an affine chart of the base -/

/-- **The dependent product along a representable thickening is a formal algebraic space as
soon as it is one over every affine formal algebraic space.** This is the reduction the source
of Stacks 0DEG performs: "take an étale covering `{X_i ⟶ X}` as in Definition 0AIM ... then
`U_{V, ψ} ×_X X_i = U_{V_i, ψ_i}` ... it suffices to show each `U_{V_i, ψ_i}` is an affine
formal algebraic space".

The covering of `U_{V, ψ}` is the base change of an affine étale atlas of `X`, which is
representable étale and jointly surjective by Stacks 0AJ1, and each of its members is
identified with the dependent product over the corresponding chart by
`AlgebraicGeometry.FormalSpace.isPullback_liftAlongBaseChange`. The set-theoretic condition of
Stacks 0AIS is *not* assumed: it descends to `U_{V, ψ}` from `X` along the representable
morphism `U_{V, ψ} ⟶ X`, which is representable because it is representable étale. -/
theorem isFormalAlgebraicSpace_liftAlong_of_affine {X I W : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) {i : I ⟶ X} {p : W ⟶ I}
    (hirep : Space.IsRepresentableThickeningULift.{u + 1} B S hS i.hom)
    (hp : IsRepresentableEtale B S hS p)
    (haff : ∀ (Y I' W' : FppfSheaf B S hS) (i' : I' ⟶ Y) (p' : W' ⟶ I'),
      IsAffineFormalAlgebraicSpace B S hS Y →
      Space.IsRepresentableThickeningULift.{u + 1} B S hS i'.hom →
      IsRepresentableEtale B S hS p' →
      IsFormalAlgebraicSpace B S hS (liftAlong B S hS i' p')) :
    IsFormalAlgebraicSpace B S hS (liftAlong B S hS i p) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨hXset, J, Y, v, hYaff, hvet, hvsurj⟩ := hX
  have hbrep : IsRepresentableEtale B S hS (liftAlongBase B S hS i p) :=
    isRepresentableEtale_liftAlongBase B S hS hirep hp
  refine isFormalAlgebraicSpace_of_etaleCover B S hS (liftAlong B S hS i p)
    (fun j ↦ Limits.pullback (v j) (liftAlongBase B S hS i p))
    (fun j ↦ pullback.snd (v j) (liftAlongBase B S hS i p)) (fun j ↦ ?_)
    (fun j ↦ isRepresentableEtale_pullback_snd B S hS (v j)
      (liftAlongBase B S hS i p) (hvet j))
    (Sheaf.isLocallySurjective_sigmaDesc_pullback_snd (liftAlongBase B S hS i p) v hvsurj)
    (SetTheoreticDescent.satisfiesSetTheoreticCondition_of_representable_over B S hS
      (liftAlongBase B S hS i p) hbrep.1 hXset)
  -- the chart of the base, and the base change of `i` and of `p` to it
  have hI' : IsPullback (pullback.snd i (v j)) (pullback.fst i (v j)) (v j) i :=
    (IsPullback.of_hasPullback i (v j)).flip
  have hi'thick : Space.IsRepresentableThickeningULift.{u + 1} B S hS
      (pullback.snd i (v j)).hom :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hI'.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1)))) hirep
  have hIex : IsSectionwisePullback B S hS (pullback.snd i (v j)) (pullback.fst i (v j))
      (v j) i := isSectionwisePullback_of_isPullback B S hS hI'
  have hWex : IsSectionwisePullback B S hS (pullback.snd p (pullback.fst i (v j)))
      (pullback.fst p (pullback.fst i (v j))) (pullback.fst i (v j)) p :=
    isSectionwisePullback_of_isPullback B S hS
      (IsPullback.of_hasPullback p (pullback.fst i (v j))).flip
  have hp' : IsRepresentableEtale B S hS (pullback.snd p (pullback.fst i (v j))) :=
    isRepresentableEtale_pullback_snd B S hS p (pullback.fst i (v j)) hp
  have hbc := isPullback_liftAlongBaseChange (pullback.fst p (pullback.fst i (v j))) hIex hWex
    hI'.w pullback.condition
  refine isFormalAlgebraicSpace_of_iso B S hS
    ((IsPullback.of_hasPullback (v j) (liftAlongBase B S hS i p)).isoIsPullback _ _ hbc.flip)
    (haff (Y j) _ _ (pullback.snd i (v j)) (pullback.snd p (pullback.fst i (v j)))
      (hYaff j) hi'thick hp')

/-! ### Stacks 0DEG: what essential surjectivity now reduces to -/

/-- **Essential surjectivity of the comparison functor of Stacks 0DEG, granting only that
`U_{V, ψ}` is a formal algebraic space.** Of the two assertions the source makes about the
quasi-inverse — that `U_{V, ψ}` is a formal algebraic space, and the omitted verification that
`U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale — the second is proved, in
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_spacesEtaleQuasiInverseBase`, and the first
is the hypothesis `hU` here.

Nothing else is assumed: the reduction of `U_{V, ψ}` is `V` itself, by
`AlgebraicGeometry.FormalSpace.isPullback_spacesEtaleQuasiInverseSection` together with Stacks
0GB7 — an étale morphism being smooth — and the morphism of reductions it induces to `X_red` is
`ψ`, by the characterisation `AlgebraicGeometry.FormalSpace.Reduction.eq_map`. -/
theorem essSurj_spacesEtaleComparison_of_isFormalAlgebraicSpace_quasiInverse
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (hU : ∀ V : R.SpacesEtale,
      IsFormalAlgebraicSpace B S hS (spacesEtaleQuasiInverse B S hS R V)) :
    (spacesEtaleComparison hX R).EssSurj := by
  refine essSurj_spacesEtaleComparison_of_exists_reduction hX R fun V ↦ ?_
  have hφ : IsRepresentableEtale B S hS (spacesEtaleQuasiInverseBase B S hS R V) :=
    isRepresentableEtale_spacesEtaleQuasiInverseBase B S hS R V
  have hsq := isPullback_spacesEtaleQuasiInverseSection B S hS R V
  have hred : IsReduction B S hS (spacesEtaleQuasiInverse B S hS R V)
      (liftSheaf B S hS V.obj.left) (spacesEtaleQuasiInverseSection B S hS R V) :=
    isReduction_pullback_reduction_of_smooth B S hS (hU V) hX hφ.1
      (hasPropertyULift_smooth_of_isRepresentableEtale B S hS hφ) R.isReduction hsq
  refine ⟨spacesEtaleQuasiInverse B S hS R V, spacesEtaleQuasiInverseBase B S hS R V,
    hU V, hφ, ⟨V.obj.left, spacesEtaleQuasiInverseSection B S hS R V, hred⟩,
    Iso.refl V.obj.left, ?_⟩
  refine (Category.id_comp V.obj.hom).trans ?_
  exact Reduction.eq_map
    (⟨V.obj.left, spacesEtaleQuasiInverseSection B S hS R V, hred⟩ :
      Reduction B S hS (spacesEtaleQuasiInverse B S hS R V))
    R (spacesEtaleQuasiInverseBase B S hS R V) V.obj.hom hsq.w.symm

/-- **Essential surjectivity of the comparison functor of Stacks 0DEG, granting only the affine
case of the source's assertion about `U_{V, ψ}`.** Of everything the source does to produce the
quasi-inverse, this leaves open one statement: that the dependent product along a representable
thickening of an *affine* formal algebraic space is a formal algebraic space — the source's "it
suffices to show that each `U_{V_i, ψ_i}` is an affine formal algebraic space", which it settles
by the proof of Stacks 0DEE. It is proved in
`StacksFrontier/AlgebraicGeometry/FormalSpace/LiftAlongAffineBase.lean`, as
`AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_liftAlong_of_isAffineFormalAlgebraicSpace`,
which is what makes `AlgebraicGeometry.FormalSpace.essSurj_spacesEtaleComparison`
unconditional; the hypothesis is kept here because the proof of the affine case sits above this
module in import order.

Everything else is proved in this module and the ones below it: the construction of `U_{V, ψ}`
and its sheaf property, that its fibre product with `X_red` over `X` is `V`, that
`U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale, that the construction commutes
with base change, that the reduction of `U_{V, ψ}` is `V` with `ψ` for its morphism to `X_red`,
and the descent of the set-theoretic condition of Stacks 0AIS from `X`. -/
theorem essSurj_spacesEtaleComparison_of_affine {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (haff : ∀ (Y I' W' : FppfSheaf B S hS) (i' : I' ⟶ Y) (p' : W' ⟶ I'),
      IsAffineFormalAlgebraicSpace B S hS Y →
      Space.IsRepresentableThickeningULift.{u + 1} B S hS i'.hom →
      IsRepresentableEtale B S hS p' →
      IsFormalAlgebraicSpace B S hS (liftAlong B S hS i' p')) :
    (spacesEtaleComparison hX R).EssSurj :=
  essSurj_spacesEtaleComparison_of_isFormalAlgebraicSpace_quasiInverse B S hS hX R
    (fun V ↦ isFormalAlgebraicSpace_liftAlong_of_affine B S hS hX
      R.isReduction.isRepresentableThickening
      (isRepresentableEtale_liftSheafMap B S hS V.obj.hom V.property) haff)

end AlgebraicGeometry.FormalSpace

end
