module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LowerShriekModules

/-!
# The sections of a sheafification on `CRIS(X/S)` over an object, read on the Zariski site

Fix a global crystalline situation and an object `B = (U, T, δ)` of the big crystalline site
`CRIS(X/S)`.  The restrictions of `B` to the opens of `T` form a functor
`T.Opens ⥤ CRIS(X/S)` which is continuous and cocontinuous
(`...Thickening.restrictOpenFunctor_isContinuous` and `..._isCocontinuous`).  So a morphism of
abelian presheaves on `CRIS(X/S)` which is locally injective and locally surjective restricts to
one on the Zariski site of `T`, and the restriction of a sheaf is a Zariski sheaf.  This is the
big-site twin of `SmallSite/SheafifySections.lean`, at the coefficient universe `u + 1` of the
module-level lower shriek.

The last result is a comparison criterion on the Zariski site of a scheme: two locally bijective
morphisms out of one presheaf into two sheaves are bijective on the same sections.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `isLocallyInjective_toSheafifyBig`, `isLocallySurjective_toSheafifyBig` — the sheafification
  unit on `CRIS(X/S)` at the coefficient universe `u + 1` is locally bijective.
* `isLocallyInjective_whiskerLeft_restrictOpenFunctorBig`,
  `isLocallySurjective_whiskerLeft_restrictOpenFunctorBig` — restriction to the ambient scheme of
  an object preserves local injectivity and local surjectivity.
* `isSheaf_restrictOpenFunctorBig` — the restriction of a sheaf is a Zariski sheaf.
* `bijective_app_of_isLocallyBijective` — the comparison criterion on the Zariski site of a
  scheme.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-- **The sheafification unit of an abelian presheaf on `CRIS(X/S)` is locally injective**, at the
coefficient universe `u + 1`. -/
theorem isLocallyInjective_toSheafifyBig (P : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallyInjective (topology S) (toSheafify (topology S) P) :=
  GrothendieckTopology.W.isLocallyInjective ((topology S).W_toSheafify P)

/-- **The sheafification unit of an abelian presheaf on `CRIS(X/S)` is locally surjective**, at
the coefficient universe `u + 1`. -/
theorem isLocallySurjective_toSheafifyBig (P : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Presheaf.IsLocallySurjective (topology S) (toSheafify (topology S) P) :=
  GrothendieckTopology.W.isLocallySurjective ((topology S).W_toSheafify P)

variable {P Q : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}

/-- **Restriction to the ambient scheme of an object of `CRIS(X/S)` preserves local
injectivity** of a morphism of abelian presheaves. -/
theorem isLocallyInjective_whiskerLeft_restrictOpenFunctorBig (B : Thickening S) (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective (topology S) η] :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (Functor.whiskerLeft B.restrictOpenFunctor.op η) :=
  Presheaf.isLocallyInjective_whisker
    (Opens.grothendieckTopology B.thickening.target.scheme) (topology S)
    B.restrictOpenFunctor η

/-- **Restriction to the ambient scheme of an object of `CRIS(X/S)` preserves local
surjectivity** of a morphism of abelian presheaves. -/
theorem isLocallySurjective_whiskerLeft_restrictOpenFunctorBig (B : Thickening S) (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective (topology S) η] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology B.thickening.target.scheme)
      (Functor.whiskerLeft B.restrictOpenFunctor.op η) :=
  Presheaf.isLocallySurjective_whisker
    (Opens.grothendieckTopology B.thickening.target.scheme) (topology S)
    B.restrictOpenFunctor η

/-- **The restriction of a sheaf on `CRIS(X/S)` to the ambient scheme of an object is a Zariski
sheaf**, the restrictions to the opens forming a continuous functor. -/
theorem isSheaf_restrictOpenFunctorBig (B : Thickening S)
    {Z : (Thickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (hZ : Presheaf.IsSheaf (topology S) Z) :
    Presheaf.IsSheaf (Opens.grothendieckTopology B.thickening.target.scheme)
      (B.restrictOpenFunctor.op ⋙ Z) :=
  B.restrictOpenFunctor.op_comp_isSheaf_of_isSheaf _ _ Z hZ

/-- **On the Zariski site of a scheme, two locally bijective morphisms out of one presheaf into
two sheaves are bijective on the same sections.**  Both are sheafifications of the presheaf, so
the second factors through the first by an isomorphism of sheaves. -/
theorem bijective_app_of_isLocallyBijective {X : Scheme.{u}}
    {R Z₁ Z₂ : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}}
    (hZ₁ : Presheaf.IsSheaf (Opens.grothendieckTopology X) Z₁)
    (hZ₂ : Presheaf.IsSheaf (Opens.grothendieckTopology X) Z₂) (φ₁ : R ⟶ Z₁) (φ₂ : R ⟶ Z₂)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ₁]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₁]
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ₂]
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ₂] (V : (X.Opens)ᵒᵖ)
    (h₁ : Function.Bijective (ConcreteCategory.hom (φ₁.app V))) :
    Function.Bijective (ConcreteCategory.hom (φ₂.app V)) := by
  have := Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective.{u, u + 1}
    X.toLocallyRingedSpace.toRingedSpace
  have hW₁ : (Opens.grothendieckTopology X).W φ₁ :=
    GrothendieckTopology.W_of_isLocallyBijective _ φ₁
  obtain ⟨θ, hθ⟩ : ∃ θ : Z₁ ⟶ Z₂, φ₁ ≫ θ = φ₂ :=
    ⟨_, (ObjectProperty.isLocal.homEquiv hW₁ Z₂ hZ₂).apply_symm_apply φ₂⟩
  have : IsIso θ := (ObjectProperty.isLocal_iff_isIso _ θ hZ₁ hZ₂).1
    (MorphismProperty.of_precomp _ _ _ hW₁ (by
      rw [hθ]
      exact GrothendieckTopology.W_of_isLocallyBijective _ φ₂))
  subst hθ
  exact (show ConcreteCategory.hom ((φ₁ ≫ θ).app V) =
      ConcreteCategory.hom (θ.app V) ∘ ConcreteCategory.hom (φ₁.app V) from
    funext fun x ↦ ConcreteCategory.comp_apply _ _ x) ▸
      (ConcreteCategory.bijective_of_isIso (θ.app V)).comp h₁

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
