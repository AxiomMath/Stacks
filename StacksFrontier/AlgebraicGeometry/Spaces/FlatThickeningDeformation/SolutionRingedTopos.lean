module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatThickeningDeformation.ClassesMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleTensorPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposIsoOverBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FpqcLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SmallEtaleRingedToposThickening
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingForget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.RecoveryOverBase
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# A flat deformation as a ringed topos on the small étale site of the source

Let `D = (f' : X' ⟶ Y', i : X ⟶ X')` be a flat deformation of `f : X ⟶ Y` over the first order
thickening `Y ⊂ Y'`. Then `i` is a thickening of algebraic spaces (a base change of `Y ⊂ Y'`), so
the direct image along `i` is an equivalence of small étale topoi (Stacks 05ZM). For a sheaf of
rings `𝒜` on `X_étale` with a ring map `φ : i⁻¹𝒪_{X'} ⟶ 𝒜`, the pair `(i_small, φ)` is a morphism
of ringed topoi `(Sh(X_étale), 𝒜) ⟶ (Sh(X'_étale), 𝒪_{X'})`, an isomorphism when `φ` is. This is
the identification `𝒪_{X'} = 𝒜` of the proof of [Stacks Project, Tag 0D17] through which an
isomorphism of solutions becomes a morphism of ringed topoi `X'_D ⟶ X'_E`.

## Main definitions
* `AlgebraicGeometry.Space.FlatThickeningDeformation.withRingsHom`.

## References
* [Stacks Project, Tag 0D17](https://stacks.math.columbia.edu/tag/0D17)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space.FlatThickeningDeformation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The adjunction computation behind the commuting square of `transportHom`: the adjunct of
`s`, followed by the direct image of `j`, of `L_D(f_D)` and of the counit, is the adjunct of
`s ≫ j ≫ L_D(f_D) ≫ ε`. -/
theorem homEquiv_comp_map_counit {𝒜 ℬ ℬ' : Type*} [Category 𝒜] [Category ℬ] [Category ℬ']
    {LE : ℬ ⥤ 𝒜} {RE : 𝒜 ⥤ ℬ} (adjE : LE ⊣ RE) {LD : ℬ' ⥤ 𝒜} {RD : 𝒜 ⥤ ℬ'} (adjD : LD ⊣ RD)
    {OE : ℬ} {OD : ℬ'} {AD OX : 𝒜} (s : LE.obj OE ⟶ AD) (j : AD ⟶ LD.obj OD)
    (fD : OD ⟶ RD.obj OX) (rE : LE.obj OE ⟶ OX)
    (h : s ≫ j ≫ (adjD.homEquiv _ _).symm fD = rE) (φ : RE.obj (LD.obj OD) ⟶ RE.obj (LD.obj
      (RD.obj OX))) (hφ : φ = RE.map (LD.map fD)) (ε : RE.obj (LD.obj (RD.obj OX)) ⟶ RE.obj OX)
    (hε : ε = RE.map (adjD.counit.app OX) ≫ 𝟙 _) :
    ((adjE.homEquiv _ _ s ≫ RE.map j) ≫ φ) ≫ ε = adjE.homEquiv _ _ rE := by
  rw [hφ, hε, ← h, Adjunction.homEquiv_counit, adjE.homEquiv_unit, adjE.homEquiv_unit]
  simp only [Category.assoc, Functor.map_comp, Category.comp_id]

/-- **The mate computation behind the composition law**: for adjunctions `L_g ⊣ R_g`, `L_i ⊣ R_i`,
`L_h ⊣ R_h` and `α : R_i ⋙ R_g ≅ R_h`, the adjunct of `s` followed by `R_g` of the adjunct of `y`
and by `α` is the adjunct for `L_h ⊣ R_h` of `y ∘ L_i(s)` read through the comparison
`L_h ≅ L_g ⋙ L_i` of left adjoints. -/
theorem homEquiv_comp_homEquiv_comp_app {𝒜 ℬ 𝒯 : Type*} [Category 𝒜] [Category ℬ] [Category 𝒯]
    {Lg : 𝒯 ⥤ ℬ} {Rg : ℬ ⥤ 𝒯} (aG : Lg ⊣ Rg) {Li : ℬ ⥤ 𝒜} {Ri : 𝒜 ⥤ ℬ} (aI : Li ⊣ Ri)
    {Lh : 𝒯 ⥤ 𝒜} {Rh : 𝒜 ⥤ 𝒯} (aH : Lh ⊣ Rh) (α : Ri ⋙ Rg ≅ Rh) {OT : 𝒯} {G₁ : ℬ} {M : 𝒜}
    (s : Lg.obj OT ⟶ G₁) (y : Li.obj G₁ ⟶ M) :
    (aG.homEquiv _ _ s ≫ Rg.map (aI.homEquiv _ _ y)) ≫ α.hom.app M =
      aH.homEquiv _ _ ((((aG.comp aI).ofNatIsoRight α).leftAdjointUniq aH).inv.app OT ≫
        Li.map s ≫ y) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app ((aG.comp aI).ofNatIsoRight α) aH OT
  have hb : ((aG.comp aI).ofNatIsoRight α).unit.app OT =
      aH.unit.app OT ≫ Rh.map ((((aG.comp aI).ofNatIsoRight α).leftAdjointUniq aH).inv.app OT) := by
    rw [← hu, Category.assoc, ← Rh.map_comp, Iso.hom_inv_id_app, Rh.map_id]
    exact (Category.comp_id _).symm
  have h1 : (aG.homEquiv _ _ s ≫ Rg.map (aI.homEquiv _ _ y)) ≫ α.hom.app M =
      ((aG.comp aI).ofNatIsoRight α).homEquiv _ _ (Li.map s ≫ y) := by
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv, Equiv.trans_apply,
      aI.homEquiv_naturality_left, aG.homEquiv_naturality_right]
  rw [h1, Adjunction.homEquiv_unit, hb, aH.homEquiv_unit, Category.assoc, ← Rh.map_comp]

section CompIso

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

universe v₁ u₁ w₁

variable {X₀ X₁ X₂ : RingedTopos.{v₁, u₁, w₁}}
  [X₀.J.HasSheafCompose (forget RingCat.{w₁})] [X₁.J.HasSheafCompose (forget RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₁})]
  [X₀.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₁} RingCat.{w₁})]

/-- The structure map of a morphism of ringed topoi is an isomorphism as soon as its underlying
map of sheaves of types is. -/
private theorem isIso_fSharp_of_isIso_forgetFSharp (f : RingedToposHom X₀ X₁)
    [IsIso (RingedToposHom.forgetFSharp f)] : IsIso f.fSharp := by
  have : IsIso (X₁.forgetRing.map f.fSharp) := ‹IsIso (RingedToposHom.forgetFSharp f)›
  exact isIso_of_reflects_iso _ X₁.forgetRing

/-- A composite of morphisms of ringed topoi with invertible structure maps has an invertible
structure map. -/
theorem isIso_comp_fSharp (g : RingedToposHom X₁ X₂) (f : RingedToposHom X₀ X₁) [IsIso g.fSharp]
    [IsIso f.fSharp] : IsIso (g.comp f).fSharp := by
  have : IsIso (RingedToposHom.forgetFSharp (g.comp f)) := by
    rw [RingedToposHom.forgetFSharp_comp]
    have : IsIso (RingedToposHom.forgetFSharp g) := Functor.map_isIso _ g.fSharp
    have : IsIso (RingedToposHom.forgetFSharp f) := Functor.map_isIso _ f.fSharp
    infer_instance
  exact isIso_fSharp_of_isIso_forgetFSharp _

end CompIso

section RingedGeneric

universe v₀ u₀ w₀

variable {X X₁ X₂ : RingedTopos.{v₀, u₀, w₀}}
  [X.J.HasSheafCompose (forget RingCat.{w₀})] [X₁.J.HasSheafCompose (forget RingCat.{w₀})]
  [X₂.J.HasSheafCompose (forget RingCat.{w₀})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [X₁.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [X₂.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [X.J.HasSheafCompose (forget CommRingCat.{w₀})] [X₁.J.HasSheafCompose (forget CommRingCat.{w₀})]
  [X₂.J.HasSheafCompose (forget CommRingCat.{w₀})]

/-- The ringed topos `(Sh(𝒞), 𝒜)`: the topos of `X` with the sheaf of rings `𝒜`. -/
abbrev withRings (X : RingedTopos.{v₀, u₀, w₀}) (A : Sheaf X.J CommRingCat.{w₀}) :
    RingedTopos.{v₀, u₀, w₀} :=
  ⟨X.C, X.J, A⟩

/-- **The morphism of ringed topoi `(i, φ) : (Sh(𝒞), 𝒜) ⟶ X₁`** with the underlying morphism of
topoi of `i` and inverse-image structure map `φ : i⁻¹𝒪_{X₁} ⟶ 𝒜`. -/
def withRingsHom (i : RingedToposHom X X₁) {A : Sheaf X.J CommRingCat.{w₀}}
    (φ : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) :
    RingedToposHom (withRings X A) X₁ where
  toToposHom := i.toToposHom
  fSharp := (commRingImageAdjunction i.toToposHom).homEquiv X₁.O A φ

variable (i : RingedToposHom X X₁) {A : Sheaf X.J CommRingCat.{w₀}}

omit [X.J.HasSheafCompose (forget CommRingCat.{w₀})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{w₀})] in
/-- The inverse-image structure map of `withRingsHom i φ` is `φ`. -/
theorem withRingsHom_fSharpInverseImage
    (φ : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) :
    (withRingsHom i φ).fSharpInverseImage = φ :=
  Equiv.symm_apply_apply _ _

/-- On underlying sheaves of types, the structure map of `(i, φ)` is the adjunct along
`i⁻¹ ⊣ i_*` of `φ`. -/
theorem forgetFSharp_withRingsHom
    (φ : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) :
    RingedToposHom.forgetFSharp (A := withRings X A) (withRingsHom i φ) =
      i.toToposHom.adj.homEquiv _ _ ((sheafCompose X.J (forget CommRingCat.{w₀})).map φ) :=
  forget_map_commRingImageAdjunction_homEquiv _ _ _ φ

/-- `(i, φ)` is an isomorphism of ringed topoi when `i_*` is an equivalence and `φ` an
isomorphism. -/
instance isEquivalence_withRingsHom [h : i.toToposHom.pushforward.IsEquivalence]
    (φ : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) :
    (withRingsHom i φ).toToposHom.pushforward.IsEquivalence :=
  h

/-- The structure map of `(i, φ)` is an isomorphism when `i_*` is an equivalence and `φ` an
isomorphism. -/
theorem isIso_withRingsHom_fSharp [i.toToposHom.pushforward.IsEquivalence]
    (φ : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) [IsIso φ] :
    IsIso (withRingsHom i φ).fSharp := by
  have hu : IsIso (i.toToposHom.adj.unit.app (X₁.forgetRing.obj X₁.O)) := inferInstance
  have : IsIso (RingedToposHom.forgetFSharp (A := withRings X A) (withRingsHom i φ)) := by
    rw [forgetFSharp_withRingsHom]
    have hR := Functor.map_isIso i.toToposHom.pushforward
      ((sheafCompose X.J (forget CommRingCat.{w₀})).map φ)
    exact (i.toToposHom.adj.homEquiv_unit _ _ _).symm ▸ @IsIso.comp_isIso _ _ _ _ _ _ _ hu hR
  exact isIso_fSharp_of_isIso_forgetFSharp _

/-- The structure map of `(i, 𝟙)` is an isomorphism when `i_*` is an equivalence. -/
theorem isIso_withRingsHom_id_fSharp [i.toToposHom.pushforward.IsEquivalence] :
    IsIso (withRingsHom i (𝟙 ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))).fSharp :=
  isIso_withRingsHom_fSharp i _

omit [X.J.HasSheafCompose (forget CommRingCat.{w₀})]
  [X₁.J.HasSheafCompose (forget CommRingCat.{w₀})] in
/-- The inverse-image structure map of `(i, 𝟙)` is an isomorphism. -/
theorem isIso_withRingsHom_id_fSharpInverseImage :
    IsIso (withRingsHom i
      (𝟙 ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))).fSharpInverseImage := by
  rw [withRingsHom_fSharpInverseImage]; exact IsIso.id _

variable (i₂ : RingedToposHom X X₂) [i.toToposHom.pushforward.IsEquivalence]
  (σ : (inverseImageCommRingFunctor i₂.toToposHom).obj X₂.O ⟶
    (inverseImageCommRingFunctor i.toToposHom).obj X₁.O)

/-- **The transport `X₁ ⟶ X₂` of an identification `σ : i₂⁻¹𝒪_{X₂} ⟶ i⁻¹𝒪_{X₁}`** along an
equivalence `i_*`: `(i₂, σ) ∘ (i, 𝟙)⁻¹`. -/
def transport : RingedToposHom X₁ X₂ :=
  letI := isIso_withRingsHom_id_fSharp i
  RingedToposHom.comp (Y := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      (withRingsHom i₂ σ)
    (RingedToposHom.inverse (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj
        X₁.O)) (withRingsHom i (𝟙 _)))

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- **The square `transport ∘ i ≅ i₂`**, when `σ` is compatible with the two structure maps. -/
def transportSquare (hσ : σ ≫ i.fSharpInverseImage = i₂.fSharpInverseImage) :
    RingedToposHom.TwoIso ((transport i i₂ σ).comp i) i₂ := by
  letI := isIso_withRingsHom_id_fSharp i
  exact
  { e := Functor.isoWhiskerRight (asIso i.toToposHom.adj.counit) i₂.toToposHom.pushforward ≪≫
      Functor.leftUnitor _
    commutes := by
      have h1 := RingedToposHom.forgetFSharp_comp (transport i i₂ σ) i
      have h2 := RingedToposHom.forgetFSharp_comp (B := withRings X ((inverseImageCommRingFunctor
          i.toToposHom).obj X₁.O)) (withRingsHom i₂ σ)
        (RingedToposHom.inverse (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj
            X₁.O)) (withRingsHom i (𝟙 _)))
      have h3 := forgetFSharp_withRingsHom i₂ σ
      have := isIso_withRingsHom_id_fSharpInverseImage i
      have hinv : inv (withRingsHom i (𝟙 _)).fSharpInverseImage = 𝟙 _ :=
        IsIso.inv_eq_of_hom_inv_id ((congrArg (· ≫ 𝟙 _)
          (withRingsHom_fSharpInverseImage i (𝟙 _))).trans (Category.comp_id _))
      have hj : RingedToposHom.forgetFSharp
          (RingedToposHom.inverse (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj
              X₁.O)) (withRingsHom i (𝟙 _))) = 𝟙 _ :=
        (congrArg X.forgetRing.map hinv).trans (X.forgetRing.map_id _)
      have ht := (RingedToposHom.fSharpInverseImage_forget_homEquiv i).symm
      have hE := RingedToposHom.fSharpInverseImage_forget_homEquiv i₂
      refine (congrArg (· ≫ _) h1).trans ?_
      refine (congrArg (fun x => (x ≫ _) ≫ _) (h2.trans (congrArg (· ≫ _) h3))).trans ?_
      refine (homEquiv_comp_map_counit i₂.toToposHom.adj i.toToposHom.adj _ _ _
        (X.forgetRing.map i₂.fSharpInverseImage) ?_ _ rfl _ ?_).trans ?_
      · exact (congrArg (_ ≫ ·) ((congrArg (· ≫ _) hj).trans ((Category.id_comp _).trans ht))).trans
          (((sheafCompose X.J (forget CommRingCat.{w₀})).map_comp _ _).symm.trans (congrArg _ hσ))
      · exact (Category.comp_id _).trans rfl
      · exact (congrArg _ hE).trans (Equiv.apply_symm_apply _ _) }

omit [X₂.J.HasSheafCompose (forget CommRingCat.{w₀})] in
/-- The direct image of `transport i i₂ σ` is an equivalence when those of `i` and `i₂` are. -/
theorem isEquivalence_transport [i₂.toToposHom.pushforward.IsEquivalence] :
    (transport i i₂ σ).toToposHom.pushforward.IsEquivalence := by
  change (i.toToposHom.inverseImage ⋙ i₂.toToposHom.pushforward).IsEquivalence
  infer_instance

/-- The structure map of `transport i i₂ σ` is an isomorphism when `i_*` and `i₂_*` are
equivalences and `σ` is an isomorphism. -/
theorem isIso_transport_fSharp [i₂.toToposHom.pushforward.IsEquivalence] [IsIso σ] :
    IsIso (transport i i₂ σ).fSharp := by
  let := isIso_withRingsHom_id_fSharp i
  have := isIso_withRingsHom_fSharp i₂ σ
  have := isIso_withRingsHom_id_fSharpInverseImage i
  have : IsIso (RingedToposHom.inverse
      (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      (withRingsHom i (𝟙 _))).fSharp :=
    (inferInstance : IsIso (inv (withRingsHom i (𝟙 _)).fSharpInverseImage))
  exact isIso_comp_fSharp _ _

section CompWithRings

variable {T : RingedTopos.{v₀, u₀, w₀}} [T.J.HasSheafCompose (forget RingCat.{w₀})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [T.J.HasSheafCompose (forget CommRingCat.{w₀})]
  (g : RingedToposHom X₁ T) (h : RingedToposHom X T)
  (α : (g.toToposHom.comp i.toToposHom).pushforward ≅ h.toToposHom.pushforward)
  (ψ : (inverseImageCommRingFunctor h.toToposHom).obj T.O ⟶
    (inverseImageCommRingFunctor i.toToposHom).obj X₁.O)
  (hψ : (sheafCompose X.J (forget CommRingCat.{w₀})).map ψ =
    (((g.toToposHom.adj.comp i.toToposHom.adj).ofNatIsoRight α).leftAdjointUniq
        h.toToposHom.adj).inv.app (T.forgetRing.obj T.O) ≫
      i.toToposHom.inverseImage.map (X₁.forgetRing.map g.fSharpInverseImage))

/-- **The composite `g ∘ (i, φ)` is `(h, ψ ≫ φ)`** up to 2-isomorphism, when the topos parts of
`g ∘ i` and `h` are identified by `α` and `ψ : h⁻¹𝒪_T ⟶ i⁻¹𝒪_{X₁}` is the inverse image along `i`
of the structure map of `g`, read through the comparison of left adjoints. -/
def compWithRingsTwoIso {A : Sheaf X.J CommRingCat.{w₀}}
    (φ : (inverseImageCommRingFunctor i.toToposHom).obj X₁.O ⟶ A) :
    RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀} (A := withRings X A)
      (RingedToposHom.comp.{v₀, u₀, w₀, v₀, u₀, w₀, v₀, u₀, w₀} (X := withRings X A) g
      (withRingsHom i φ)) (withRingsHom h (ψ ≫ φ)) where
  e := α
  commutes := by
    have h1 := RingedToposHom.forgetFSharp_comp (A := withRings X A) g (withRingsHom i φ)
    have h2 := forgetFSharp_withRingsHom i φ
    have h3 := forgetFSharp_withRingsHom h (ψ ≫ φ)
    have hg : RingedToposHom.forgetFSharp g = g.toToposHom.adj.homEquiv _ _
        (X₁.forgetRing.map g.fSharpInverseImage) :=
      ((congrArg _ (RingedToposHom.fSharpInverseImage_forget_homEquiv g)).trans
        (Equiv.apply_symm_apply _ _)).symm
    refine (congrArg (· ≫ _) (h1.trans (congrArg₂ (· ≫ ·) hg (congrArg _ h2)))).trans ?_
    refine (homEquiv_comp_homEquiv_comp_app g.toToposHom.adj i.toToposHom.adj h.toToposHom.adj
      α _ _).trans ?_
    refine Eq.trans ?_ h3.symm
    congr 1
    rw [Functor.map_comp, hψ]
    exact (Category.assoc _ _ _).symm

end CompWithRings

section Base

variable {T : RingedTopos.{v₀, u₀, w₀}} [T.J.HasSheafCompose (forget RingCat.{w₀})]
  [T.J.HasSheafCompose (forget₂ CommRingCat.{w₀} RingCat.{w₀})]
  [T.J.HasSheafCompose (forget CommRingCat.{w₀})]
  (p₁ : RingedToposHom X₁ T) (p₂ : RingedToposHom X₂ T)

/-- `p₁ ∘ ((i, 𝟙) ∘ (i, 𝟙)⁻¹) ≅ p₁`. -/
def compCompInverseTwoIso :
    letI := isIso_withRingsHom_id_fSharp i
    RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀}
      (p₁.comp ((withRingsHom i (𝟙 ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))).comp
        (RingedToposHom.inverse
          (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
          (withRingsHom i (𝟙 _))))) p₁ :=
  letI := isIso_withRingsHom_id_fSharp i
  { e := Functor.isoWhiskerRight (asIso i.toToposHom.adj.unit).symm p₁.toToposHom.pushforward ≪≫
      Functor.leftUnitor _
    commutes := by
      have h1 := RingedToposHom.forgetFSharp_comp p₁
        ((withRingsHom i (𝟙 ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))).comp
          (RingedToposHom.inverse
            (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
            (withRingsHom i (𝟙 _))))
      have h2 := RingedToposHom.forgetRing_map_comp_inverse_fSharp
        (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
        (withRingsHom i (𝟙 _))
      refine (congrArg (· ≫ _) (h1.trans (congrArg (_ ≫ p₁.toToposHom.pushforward.map ·)
          h2))).trans ?_
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ?_).trans (Category.comp_id _))
      refine (congrArg (_ ≫ ·) (Category.comp_id _)).trans ?_
      refine (p₁.toToposHom.pushforward.map_comp _ _).symm.trans ?_
      exact (congrArg _ ((asIso i.toToposHom.adj.unit).hom_inv_id_app _)).trans
        (p₁.toToposHom.pushforward.map_id _) }

/-- **The base triangle `p₂ ∘ transport ≅ p₁`**, from the corresponding 2-isomorphism on
`(Sh(𝒞), i⁻¹𝒪_{X₁})`. -/
def transportBase
    (hA : RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀}
      (A := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      (RingedToposHom.comp.{v₀, u₀, w₀, v₀, u₀, w₀, v₀, u₀, w₀}
        (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O)) p₂
        (withRingsHom i₂ σ))
      (RingedToposHom.comp.{v₀, u₀, w₀, v₀, u₀, w₀, v₀, u₀, w₀}
        (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O)) p₁
        (withRingsHom i (𝟙 _)))) :
    RingedToposHom.TwoIso.{v₀, u₀, w₀, v₀, u₀, w₀} (p₂.comp (transport i i₂ σ)) p₁ :=
  letI := isIso_withRingsHom_id_fSharp i
  (RingedToposHom.TwoIso.associator
      (B := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
      (RingedToposHom.inverse
        (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
        (withRingsHom i (𝟙 _))) (withRingsHom i₂ σ) p₂).trans
    ((RingedToposHom.TwoIso.whiskerLeft
      (RingedToposHom.inverse
        (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
        (withRingsHom i (𝟙 _))) hA).trans
      ((RingedToposHom.TwoIso.associator
        (B := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
        (RingedToposHom.inverse
          (X := withRings X ((inverseImageCommRingFunctor i.toToposHom).obj X₁.O))
          (withRingsHom i (𝟙 _))) (withRingsHom i (𝟙 _)) p₁).symm.trans
        (compCompInverseTwoIso i p₁)))

end Base

/-- The structure map of `transport i i₂ τ.hom` is an isomorphism for an isomorphism `τ`, when
`i_*` and `i₂_*` are equivalences. -/
theorem isIso_transport_fSharp_of_iso [i₂.toToposHom.pushforward.IsEquivalence]
    (τ : (inverseImageCommRingFunctor i₂.toToposHom).obj X₂.O ≅
      (inverseImageCommRingFunctor i.toToposHom).obj X₁.O) :
    IsIso (transport i i₂ τ.hom).fSharp :=
  isIso_transport_fSharp i i₂ τ.hom

end RingedGeneric

namespace Deformation

variable {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)} (D : Deformation f)

include hZ in
/-- The inclusion `i : X ⟶ X'` of a flat deformation is a thickening: it is the base change of
the thickening `Y ⊂ Y'` along `f'`. -/
theorem isThickeningHom_i : IsThickeningHom B S hS D.i :=
  (isThickeningHom_iff_isClosedImmersion_and_isSurjective B S hS D.i).2
    ⟨isClosedImmersion_of_isPullback B S hS D.isPullback.flip Z.2.2,
      isSurjective_of_isPullback B S hS D.isPullback.flip hZ.1.2⟩

include hZ in
/-- The direct image along the inclusion `i : X ⟶ X'` of a flat deformation is an equivalence of
small étale topoi. -/
theorem isEquivalence_i :
    (smallEtaleRingedToposHom B S hS D.i).toToposHom.pushforward.IsEquivalence :=
  isEquivalence_smallEtalePushforward_of_isThickeningHom (D.isThickeningHom_i hZ)

end Deformation

section SmallComp

variable {X X₁ T : AlgebraicSpaces B S hS} (i : X ⟶ X₁) (g : X₁ ⟶ T)

/-- **`g_small ∘ (i, φ) ≅ ((i ≫ g)_small, (i ≫ g)⁻¹𝒪_T ⟶ i⁻¹𝒪_{X₁} ⟶ 𝒜)`**: the composition law of
Stacks 03G8 for a morphism of ringed topoi out of `(Sh(X_étale), 𝒜)`. -/
def smallCompWithRingsTwoIso {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ : inverseImageStructureSheaf B S hS i ⟶ A) :=
  compWithRingsTwoIso.{u, u + 1, u} (i := smallEtaleRingedToposHom B S hS i)
    (smallEtaleRingedToposHom B S hS g) (smallEtaleRingedToposHom B S hS (i ≫ g))
    (smallToposMorphismTypeU_comp B S hS i g) (inverseImageStructureSheafMap B S hS i g)
    ((Functor.map_comp _ _ _).trans (congrArg₂ (· ≫ ·)
      (forget_map_compInverseImageRingIso_inv_app B S hS i g _)
      (forget_map_smallEtaleInverseImageRing_map B S hS i _))) φ

/-- Two morphisms `(r₁, φ₁)`, `(r₂, φ₂)` with `r₁ = r₂` and matching structure maps agree up to
2-isomorphism. -/
def withRingsHomEqTwoIso {r₁ r₂ : X ⟶ T} (hr : r₁ = r₂)
    {A : Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}}
    (φ₁ : inverseImageStructureSheaf B S hS r₁ ⟶ A) (φ₂ : inverseImageStructureSheaf B S hS r₂ ⟶ A)
    (hφ : φ₁ = eqToHom (congrArg (inverseImageStructureSheaf B S hS) hr) ≫ φ₂) :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (A := withRings (smallEtaleRingedTopos B S hS X) A)
      (withRingsHom (smallEtaleRingedToposHom B S hS r₁) φ₁)
      (withRingsHom (smallEtaleRingedToposHom B S hS r₂) φ₂) := by
  subst hr
  obtain rfl : φ₁ = φ₂ := hφ.trans (by rw [eqToHom_refl]; exact Category.id_comp _)
  exact RingedToposHom.TwoIso.refl.{u, u + 1, u, u, u + 1, u} _

end SmallComp

/-- If `(c ≫ eqToHom p₁ ≫ M₁) ≫ σ.hom = c ≫ eqToHom p₂ ≫ M₂` for an isomorphism `c`, then
`M₂ ≫ σ.inv = eqToHom (p₂.symm.trans p₁) ≫ M₁ ≫ 𝟙 _`. -/
theorem eqToHom_cancel_aux {𝒞 : Type*} [Category 𝒞] {A B C₁ C₂ P Q : 𝒞} (c : A ≅ B)
    (p₁ : B = C₁) (p₂ : B = C₂) (M₁ : C₁ ⟶ P) (M₂ : C₂ ⟶ Q) (σ : P ≅ Q)
    (h : (c.hom ≫ eqToHom p₁ ≫ M₁) ≫ σ.hom = c.hom ≫ eqToHom p₂ ≫ M₂) :
    M₂ ≫ σ.inv = eqToHom (p₂.symm.trans p₁) ≫ M₁ ≫ 𝟙 _ := by
  subst p₁ p₂
  have h' := (cancel_epi c.hom).1 ((Category.assoc _ _ _).symm.trans h)
  simp only [eqToHom_refl, Category.id_comp] at h'
  simp [← h']

section Transport

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem

variable {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  {f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS)} {D E : Deformation f}
  (σ : CompatibleFirstOrderThickening.Iso.{u, u + 1, u, u, u + 1, u}
    (D.ambientSolution hZ) (E.ambientSolution hZ))

/-- **The morphism of small étale ringed topoi `X'_D ⟶ X'_E` of an isomorphism of solutions**
`σ : i_D⁻¹𝒪_{X'_D} ≅ i_E⁻¹𝒪_{X'_E}`: `(i_E, σ⁻¹) ∘ (i_D, 𝟙)⁻¹`. -/
def transportHom :
    RingedToposHom (smallEtaleRingedTopos B S hS D.X') (smallEtaleRingedTopos B S hS E.X') :=
  letI := D.isEquivalence_i hZ
  transport.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
    (smallEtaleRingedToposHom B S hS E.i)
    σ.hom.symm.hom

/-- `transportHom hZ σ` is an isomorphism of ringed topoi: its direct image is an equivalence and
its structure map an isomorphism. -/
theorem isIso_transportHom :
    (transportHom hZ σ).toToposHom.pushforward.IsEquivalence ∧
      IsIso (transportHom hZ σ).fSharp := by
  let := D.isEquivalence_i hZ
  have := E.isEquivalence_i hZ
  exact ⟨isEquivalence_transport.{u, u + 1, u} _ _ _,
    isIso_transport_fSharp_of_iso.{u, u + 1, u} _ _ σ.hom.symm⟩

/-- `transportHom hZ σ` is a morphism of locally ringed topoi. -/
theorem isLocallyRinged_transportHom : (transportHom hZ σ).IsLocallyRinged := by
  have := (isIso_transportHom hZ σ).1
  have := (isIso_transportHom hZ σ).2
  exact isLocallyRinged_of_smallEtaleRingedToposIso B S hS _

/-- **The square `Φ ∘ i_D ≅ i_E`**: on `X` the transported morphism is the inclusion of `X` into
`X'_E`, since `σ` is compatible with the reductions. -/
def transportSquareTwoIso :
    SmallEtaleTwoIso B S hS (smallEtaleComp B S hS (transportHom hZ σ)
      (smallEtaleRingedToposHom B S hS D.i)) (smallEtaleRingedToposHom B S hS E.i) :=
  letI := D.isEquivalence_i hZ
  transportSquare.{u, u + 1, u} _ _ _ (by
    change σ.hom.symm.hom ≫ structureSharpInverseImage B S hS D.i =
      structureSharpInverseImage B S hS E.i
    rw [← Deformation.ambientSolution_reduction hZ D, ← σ.reduction_comm,
      Deformation.ambientSolution_reduction hZ E]
    exact σ.hom.inv_hom_id_assoc _)

/-- `f'_E ∘ (i_E, σ⁻¹) ≅ f'_D ∘ (i_D, 𝟙)` as morphisms out of `(Sh(X_étale), i_D⁻¹𝒪_{X'_D})`,
since `σ` is compatible with the maps from the thickened base. -/
def transportBaseAux :
    RingedToposHom.TwoIso.{u, u + 1, u, u, u + 1, u}
      (A := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (X := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
        (smallEtaleRingedToposHom B S hS E.f')
        (withRingsHom (smallEtaleRingedToposHom B S hS E.i) σ.hom.symm.hom))
      (RingedToposHom.comp.{u, u + 1, u, u, u + 1, u, u, u + 1, u}
        (X := withRings (smallEtaleRingedTopos B S hS X) (inverseImageStructureSheaf B S hS D.i))
        (smallEtaleRingedToposHom B S hS D.f')
        (withRingsHom (smallEtaleRingedToposHom B S hS D.i) (𝟙 _))) := by
  have hb := eqToHom_cancel_aux ((smallEtaleRingedToposHom_compInverseImageRingIso B S hS f
      (subspaceInclusion B S hS Y' Z)).app (smallEtaleRingedTopos B S hS Y').O) _ _
    (inverseImageStructureSheafMap B S hS D.i D.f')
    (inverseImageStructureSheafMap B S hS E.i E.f') σ.hom
    ((congrArg (· ≫ σ.hom.hom) (Deformation.ambientSolution_baseMap hZ D).symm).trans
      (σ.baseMap_comm.trans (Deformation.ambientSolution_baseMap hZ E)))
  exact (smallCompWithRingsTwoIso E.i E.f' σ.hom.symm.hom).trans
    ((withRingsHomEqTwoIso (E.isPullback.w.trans D.isPullback.w.symm) _ _ hb).trans
      (smallCompWithRingsTwoIso D.i D.f' (𝟙 _)).symm)

/-- **The triangle `f'_E ∘ Φ ≅ f'_D`**: the transported morphism lies over `Y'`. -/
def transportBaseTwoIso :
    SmallEtaleTwoIso B S hS (smallEtaleComp B S hS (smallEtaleRingedToposHom B S hS E.f')
      (transportHom hZ σ)) (smallEtaleRingedToposHom B S hS D.f') :=
  letI := D.isEquivalence_i hZ
  transportBase.{u, u + 1, u} (smallEtaleRingedToposHom B S hS D.i)
    (smallEtaleRingedToposHom B S hS E.i) σ.hom.symm.hom (smallEtaleRingedToposHom B S hS D.f')
    (smallEtaleRingedToposHom B S hS E.f') (transportBaseAux hZ σ)

include σ in
/-- **Isomorphic solutions come from isomorphic deformations** (the injectivity half of the proof
of Stacks 0D17): by Stacks 04KL over the base `Y'` the transported morphism `Φ : X'_D ⟶ X'_E` of
small étale ringed topoi, which lies over `Y'`, is induced by a morphism `k : X'_D ⟶ X'_E` over
`Y'`; `k` restricts to `X ⟶ X'_E` along `i_D` because `Φ` does, and it is an isomorphism because
`Φ` is an isomorphism of ringed topoi (Stacks 05ZN with Stacks 04KL). -/
theorem nonempty_hom_of_iso : Nonempty (D ⟶ E) := by
  have hKL : IsRecoveredFromSmallEtale B S hS := isRecoveredFromSmallEtale_holds B S hS
  obtain ⟨k, ⟨t⟩, -⟩ := hKL D.f' E.f' (transportHom hZ σ) (isLocallyRinged_transportHom hZ σ)
    ⟨transportBaseTwoIso hZ σ⟩
  have hi : D.i ≫ k = E.i := eq_of_inducesSmallEtaleRingedToposHom B S hS hKL _ _
    ⟨(smallEtaleRingedToposHomCompTwoIso B S hS D.i k).symm.trans
      ((RingedToposHom.TwoIso.whiskerLeft (smallEtaleRingedToposHom B S hS D.i) t).trans
        (transportSquareTwoIso hZ σ))⟩
  have hf : k ≫ E.f' = D.f' := eq_of_inducesSmallEtaleRingedToposHom B S hS hKL _ _
    ⟨(smallEtaleRingedToposHomCompTwoIso B S hS k E.f').symm.trans
      ((RingedToposHom.TwoIso.whiskerRight t (smallEtaleRingedToposHom B S hS E.f')).trans
        (transportBaseTwoIso hZ σ))⟩
  have := (isIso_transportHom hZ σ).1
  have := (isIso_transportHom hZ σ).2
  have : (smallEtaleRingedToposHom B S hS k).toToposHom.pushforward.IsEquivalence :=
    Functor.isEquivalence_of_iso t.e.symm
  have : IsIso (smallEtaleRingedToposHom B S hS k).fSharp := by
    have hc : RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS k) =
        RingedToposHom.forgetFSharp (transportHom hZ σ) ≫ t.e.inv.app _ := by
      rw [← t.commutes, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have : IsIso (RingedToposHom.forgetFSharp (transportHom hZ σ)) :=
      Functor.map_isIso _ (transportHom hZ σ).fSharp
    have : IsIso (RingedToposHom.forgetFSharp (smallEtaleRingedToposHom B S hS k)) := by
      rw [hc]; infer_instance
    exact isIso_fSharp_of_isIso_forgetFSharp (smallEtaleRingedToposHom B S hS k)
  have := isIso_of_isIso_smallEtaleRingedToposHom k
  exact ⟨{ hom := asIso k, hom_f' := hf, compat := hi }⟩

end Transport

section Injective

open _root_.Deformation.ToposThickening.RingedToposExtensionProblem

variable {Y' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS Y'.1}
  (hZ : IsFirstOrderThickening B S hS Y' Z.1) {X : AlgebraicSpaces B S hS}
  (f : X ⟶ (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces B S hS))

/-- **The map from isomorphism classes of flat deformations to isomorphism classes of solutions
is injective.** -/
theorem classesMap_injective : Function.Injective (classesMap hZ f) := by
  intro a b h
  induction a using Quotient.inductionOn with | h D => ?_
  induction b using Quotient.inductionOn with | h E => ?_
  obtain ⟨σ⟩ := Quotient.exact
    (s := CompatibleFirstOrderThickening.isomorphicSetoid.{u, u + 1, u, u, u + 1, u}
      (problem f hZ)) h
  exact Quotient.sound (nonempty_hom_of_iso hZ σ)

end Injective

end AlgebraicGeometry.Space.FlatThickeningDeformation

end
