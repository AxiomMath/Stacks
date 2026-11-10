module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackCongrOfSiteIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionOfDirectImages
public import StacksFrontier.CategoryTheory.Sites.Modules.CoefficientChange

/-!
# Morphisms of constant ringed topoi

Let `R` be a commutative ring and `(C, J)` a small site. The constant ringed topos `(Sh(C), R̲)`
has the sheafification of the constant presheaf of rings on `R` as its structure sheaf. A
continuous functor `u : D ⥤ C` between the underlying sites of two constant ringed topoi is a
morphism of ringed topoi `(Sh(C), R̲) ⟶ (Sh(D), R̲)` with the structure map `R̲ ⟶ u_*R̲` induced by
the sheafification unit (`constantHom`). Such structure maps are determined by the sheafification
unit, so any two morphisms between constant ringed topoi whose structure maps are of this kind
are isomorphic as soon as their underlying functors are, and the composite of two of them is
again of this kind.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom.constantRingedTopos`: the constant ringed topos.
* `AlgebraicGeometry.RingedToposSiteHom.IsConstantFSharp`: the structure map sends the image of a
  constant to the image of the same constant.
* `AlgebraicGeometry.RingedToposSiteHom.constantHom`: the morphism of constant ringed topoi of a
  continuous functor.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.fSharpCompatible_of_isConstantFSharp`: two morphisms of
  constant ringed topoi with constant structure maps are compatible along any isomorphism of their
  underlying functors.
* `AlgebraicGeometry.RingedToposSiteHom.isConstantFSharp_comp`: composites keep constant structure
  maps.
* `AlgebraicGeometry.RingedToposSiteHom.pushforwardToposEquivalence`: two morphisms with constant
  structure maps whose underlying functors are mutually inverse up to isomorphism have mutually
  inverse pushforwards of sheaves of modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace AlgebraicGeometry.RingedToposSiteHom

section Constant

variable {C D E : Type w} [SmallCategory C] [SmallCategory D] [SmallCategory E]
  (R : CommRingCat.{w})

/-- **The constant ringed topos `(Sh(C), R̲)`** of a small site. -/
abbrev constantRingedTopos (J : GrothendieckTopology C) [HasWeakSheafify J CommRingCat.{w}] :
    RingedTopos.{w, w, w} where
  C := C
  J := J
  O := (constantSheaf J CommRingCat.{w}).obj R

variable {R} {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  {JE : GrothendieckTopology E} [HasWeakSheafify JC CommRingCat.{w}]
  [HasWeakSheafify JD CommRingCat.{w}] [HasWeakSheafify JE CommRingCat.{w}]

/-- **The structure map of a morphism of constant ringed topoi is constant**: it sends the image
of a constant in `R̲` to the image of the same constant. -/
def IsConstantFSharp
    (φ : RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JD)) : Prop :=
  toSheafify JD ((Functor.const Dᵒᵖ).obj R) ≫ φ.fSharp.hom =
    Functor.whiskerLeft φ.u.op (toSheafify JC ((Functor.const Cᵒᵖ).obj R))

/-- A constant structure map sends the unit of the constant sheaf at `V` to the unit at `φ.u V`. -/
private theorem app_toSheafify_comp_fSharp
    {φ : RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JD)}
    (hφ : IsConstantFSharp φ) (V : Dᵒᵖ) :
    (toSheafify JD ((Functor.const Dᵒᵖ).obj R)).app V ≫ φ.fSharp.hom.app V =
      (toSheafify JC ((Functor.const Cᵒᵖ).obj R)).app (Opposite.op (φ.u.obj V.unop)) :=
  congr_app hφ V

/-- **Two morphisms of constant ringed topoi with constant structure maps are compatible along any
isomorphism of their underlying functors**: both structure maps are determined by the
sheafification unit, which is natural. -/
theorem fSharpCompatible_of_isConstantFSharp
    [(constantRingedTopos R JC).J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [(constantRingedTopos R JD).J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    {φ ψ : RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JD)}
    (hφ : IsConstantFSharp φ) (hψ : IsConstantFSharp ψ) (e : ψ.u ≅ φ.u) :
    FSharpCompatible φ ψ e := by
  refine Sheaf.hom_ext (sheafify_hom_ext JD _ _ (ObjectProperty.FullSubcategory.property _) ?_)
  refine NatTrans.ext (funext fun V => ?_)
  have h₁ := app_toSheafify_comp_fSharp hφ V
  have h₂ := app_toSheafify_comp_fSharp hψ V
  have hn := (toSheafify JC ((Functor.const Cᵒᵖ).obj R)).naturality (e.hom.app V.unop).op
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at hn
  change (toSheafify JD ((Functor.const Dᵒᵖ).obj R)).app V ≫ φ.fSharp.hom.app V ≫
      (sheafify JC ((Functor.const Cᵒᵖ).obj R)).map (e.hom.app V.unop).op =
    (toSheafify JD ((Functor.const Dᵒᵖ).obj R)).app V ≫ ψ.fSharp.hom.app V
  exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans (hn.symm.trans h₂.symm))

/-- **The composite of two morphisms of constant ringed topoi with constant structure maps has a
constant structure map.** -/
theorem isConstantFSharp_comp
    {f : RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JD)}
    {g : RingedToposSiteHom (constantRingedTopos R JD) (constantRingedTopos R JE)}
    (hf : IsConstantFSharp f) (hg : IsConstantFSharp g) : IsConstantFSharp (g.comp f) := by
  refine NatTrans.ext (funext fun V => ?_)
  have h₁ := app_toSheafify_comp_fSharp hg V
  have h₂ := app_toSheafify_comp_fSharp hf (Opposite.op (g.u.obj V.unop))
  change (toSheafify JE ((Functor.const Eᵒᵖ).obj R)).app V ≫ g.fSharp.hom.app V ≫
      f.fSharp.hom.app (Opposite.op (g.u.obj V.unop)) =
    (toSheafify JC ((Functor.const Cᵒᵖ).obj R)).app (Opposite.op (f.u.obj (g.u.obj V.unop)))
  exact (Category.assoc _ _ _).symm.trans ((h₁ =≫ _).trans h₂)

/-- **The morphism of constant ringed topoi `(Sh(C), R̲) ⟶ (Sh(D), R̲)` of a continuous functor
`u : D ⥤ C`**, with the structure map `R̲ ⟶ u_*R̲` induced by the sheafification unit. -/
def constantHom (u : D ⥤ C) [u.IsContinuous JD JC] :
    RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JD) where
  u := u
  fSharp := ((sheafificationAdjunction JD CommRingCat.{w}).homEquiv _ _).symm
    (Functor.whiskerLeft u.op (toSheafify JC ((Functor.const Cᵒᵖ).obj R)))

/-- The underlying functor of `constantHom u` is `u`. -/
@[simp]
theorem constantHom_u (u : D ⥤ C) [u.IsContinuous JD JC] :
    (constantHom (R := R) (JC := JC) (JD := JD) u).u = u :=
  rfl

/-- The structure map of `constantHom` is constant. -/
theorem isConstantFSharp_constantHom (u : D ⥤ C) [u.IsContinuous JD JC] :
    IsConstantFSharp (constantHom (R := R) (JC := JC) (JD := JD) u) := by
  have h := ((sheafificationAdjunction JD CommRingCat.{w}).homEquiv
    ((Functor.const _).obj R)
    ((u.sheafPushforwardContinuous CommRingCat.{w} JD JC).obj
      ((constantSheaf JC CommRingCat.{w}).obj R))).apply_symm_apply
    (Functor.whiskerLeft u.op (toSheafify JC ((Functor.const Cᵒᵖ).obj R)))
  rw [Adjunction.homEquiv_unit] at h
  exact h

/-- The identity of a constant ringed topos, as the change of coefficients along the identity. -/
abbrev constantId : RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JC) :=
  coefficientChange JC (𝟙 ((constantSheaf JC CommRingCat.{w}).obj R))

/-- The identity has a constant structure map. -/
theorem isConstantFSharp_constantId : IsConstantFSharp (constantId (R := R) (JC := JC)) :=
  Category.comp_id (toSheafify JC ((Functor.const Cᵒᵖ).obj R))

section Equivalence

variable [JC.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The pushforward of sheaves of modules along the identity of a constant ringed topos is the
identity. -/
def pushforwardToposConstantIdIso :
    (constantId (R := R) (JC := JC)).pushforwardTopos ≅ 𝟭 _ :=
  SheafOfModules.pushforwardCongr (F := 𝟭 C)
      (φ := (constantId (R := R) (JC := JC)).fSharpRing)
      (ψ := 𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((constantSheaf JC CommRingCat.{w}).obj R)))
      ((coefficientChange_fSharpRing (J := JC) (𝟙 ((constantSheaf JC CommRingCat.{w}).obj R))).trans
        (CategoryTheory.Functor.map_id (sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w}))
          ((constantSheaf JC CommRingCat.{w}).obj R))) ≪≫
    SheafOfModules.pushforwardId _

variable {φ : RingedToposSiteHom (constantRingedTopos R JC) (constantRingedTopos R JD)}
  {ψ : RingedToposSiteHom (constantRingedTopos R JD) (constantRingedTopos R JC)}

/-- **A morphism of constant ringed topoi followed by one in the other direction, whose underlying
functors compose to the identity up to isomorphism, has pushforward isomorphic to the identity**,
when both have constant structure maps. -/
def pushforwardToposCompIsoId (hφ : IsConstantFSharp φ) (hψ : IsConstantFSharp ψ)
    (e : 𝟭 C ≅ ψ.u ⋙ φ.u) :
    φ.pushforwardTopos ⋙ ψ.pushforwardTopos ≅ 𝟭 _ :=
  (pushforwardToposCompIso φ ψ).symm ≪≫
    pushforwardToposIsoOfIso (fSharpCompatible_of_isConstantFSharp (isConstantFSharp_comp hφ hψ)
      (isConstantFSharp_constantId (R := R) (JC := JC)) e) ≪≫
    pushforwardToposConstantIdIso

/-- **Morphisms of constant ringed topoi with constant structure maps and mutually inverse
underlying functors have mutually inverse pushforwards of sheaves of modules.** -/
def pushforwardToposEquivalence (hφ : IsConstantFSharp φ) (hψ : IsConstantFSharp ψ)
    (e₁ : 𝟭 C ≅ ψ.u ⋙ φ.u) (e₂ : 𝟭 D ≅ φ.u ⋙ ψ.u) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedTopos R JC).O) ≌
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (constantRingedTopos R JD).O) :=
  CategoryTheory.Equivalence.mk φ.pushforwardTopos ψ.pushforwardTopos
    (pushforwardToposCompIsoId hφ hψ e₁).symm (pushforwardToposCompIsoId hψ hφ e₂)

/-- The forward functor of `pushforwardToposEquivalence` is the pushforward along `φ`. -/
@[simp]
theorem pushforwardToposEquivalence_functor (hφ : IsConstantFSharp φ)
    (hψ : IsConstantFSharp ψ) (e₁ : 𝟭 C ≅ ψ.u ⋙ φ.u) (e₂ : 𝟭 D ≅ φ.u ⋙ ψ.u) :
    (pushforwardToposEquivalence hφ hψ e₁ e₂).functor = φ.pushforwardTopos :=
  rfl

/-- The pullback of sheaves of modules along such a morphism is an equivalence, being left
adjoint to an equivalence. -/
theorem isEquivalence_pullbackTopos [HasWeakSheafify JC AddCommGrpCat.{w}]
    [JC.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify JD AddCommGrpCat.{w}]
    [JD.WEqualsLocallyBijective AddCommGrpCat.{w}] (hφ : IsConstantFSharp φ)
    (hψ : IsConstantFSharp ψ) (e₁ : 𝟭 C ≅ ψ.u ⋙ φ.u) (e₂ : 𝟭 D ≅ φ.u ⋙ ψ.u) :
    φ.pullbackTopos.IsEquivalence :=
  have : φ.pushforwardTopos.IsEquivalence :=
    (pushforwardToposEquivalence hφ hψ e₁ e₂).isEquivalence_functor
  φ.pullbackPushforwardAdjunctionTopos.isEquivalence_left_of_isEquivalence_right

end Equivalence

end Constant

end AlgebraicGeometry.RingedToposSiteHom

end
