module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeDerivedTransport

/-!
# The hypotheses of the base change transport lemmas, as named propositions

`Stacks.Cohomology.BaseChange.mate_exactTransport_app` and
`Stacks.Cohomology.BaseChange.derived_exactTransport_app` transport a base change comparison along
functors `U` commuting with the edges of a square. Their hypotheses are equations between
composites of components. This file names the shapes of those equations
(`CompCompat`, `SquareCompat`, `NatTransCompat`) and restates the transport lemmas in their
terms, together with the step from two composition isomorphisms to a square
(`SquareCompat.of_compCompat`) and the consequence for invertibility
(`isIso_derived_app_iff_of_natTransCompat`).

## Implementation notes

The point of the names is the kernel. At the étale functors the same functor is written with two
spellings of its source or target category (the structure sheaf `etaleRing Λ X` or
`Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ X).O`, the coefficients `Ab` or
`AddCommGrpCat`). A hypothesis elaborated on its own and the corresponding binder of a transport
lemma then differ only by these spellings, but they differ under the projections `≫`, `Functor.map`
and `NatTrans.app`, which the kernel unfolds rather than compare argumentwise, and the conversion
does not finish. A hypothesis stated as one of the propositions here is compared with the binder
argument by argument, and its arguments are the functors and isomorphisms themselves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

/-! ### Composites of right adjoints -/

section Compat

variable {𝒯 𝒮 𝒳 𝒴 𝒯' 𝒮' 𝒳' 𝒴' : Type*} [Category* 𝒯] [Category* 𝒮] [Category* 𝒳]
  [Category* 𝒴] [Category* 𝒯'] [Category* 𝒮'] [Category* 𝒳'] [Category* 𝒴']
  {UY : 𝒴 ⥤ 𝒴'} {UT : 𝒯 ⥤ 𝒯'} {US : 𝒮 ⥤ 𝒮'} {UX : 𝒳 ⥤ 𝒳'}

/-- **`U` carries a factorization `ψ : P ≅ P₁ ⋙ P₂` of a functor to the factorization
`c : P₁' ⋙ P₂' ≅ P'`**, through the commutation isomorphisms `ρ₁`, `ρ₂`, `ρ` of the three functors
with the `U`'s. -/
def CompCompat {P₁ : 𝒴 ⥤ 𝒯} {P₂ : 𝒯 ⥤ 𝒮} {P : 𝒴 ⥤ 𝒮} {P₁' : 𝒴' ⥤ 𝒯'} {P₂' : 𝒯' ⥤ 𝒮'}
    {P' : 𝒴' ⥤ 𝒮'} (ρ₁ : P₁ ⋙ UT ≅ UY ⋙ P₁') (ρ₂ : P₂ ⋙ US ≅ UT ⋙ P₂') (ρ : P ⋙ US ≅ UY ⋙ P')
    (ψ : P ≅ P₁ ⋙ P₂) (c : P₁' ⋙ P₂' ≅ P') : Prop :=
  ∀ y : 𝒴, US.map (ψ.hom.app y) ≫ ρ₂.hom.app (P₁.obj y) ≫ P₂'.map (ρ₁.hom.app y) =
    ρ.hom.app y ≫ c.inv.app (UY.obj y)

/-- **`U` carries a comparison `σ : e_* ⋙ g_* ≅ h_* ⋙ f_*` of the composite right adjoints of a
square to `σ₁`**, through the commutation isomorphisms of the four functors with the `U`'s: the
hypothesis of `Stacks.Cohomology.BaseChange.mate_exactTransport_app`. -/
def SquareCompat {Pe : 𝒴 ⥤ 𝒯} {Pg : 𝒯 ⥤ 𝒮} {Ph : 𝒴 ⥤ 𝒳} {Pf : 𝒳 ⥤ 𝒮} {Pe₁ : 𝒴' ⥤ 𝒯'}
    {Pg₁ : 𝒯' ⥤ 𝒮'} {Ph₁ : 𝒴' ⥤ 𝒳'} {Pf₁ : 𝒳' ⥤ 𝒮'} (ρe : Pe ⋙ UT ≅ UY ⋙ Pe₁)
    (ρg : Pg ⋙ US ≅ UT ⋙ Pg₁) (ρh : Ph ⋙ UX ≅ UY ⋙ Ph₁) (ρf : Pf ⋙ US ≅ UX ⋙ Pf₁)
    (σ : Pe ⋙ Pg ≅ Ph ⋙ Pf) (σ₁ : Pe₁ ⋙ Pg₁ ≅ Ph₁ ⋙ Pf₁) : Prop :=
  ∀ y : 𝒴, US.map (σ.hom.app y) ≫ ρf.hom.app (Ph.obj y) ≫ Pf₁.map (ρh.hom.app y) =
    ρg.hom.app (Pe.obj y) ≫ Pg₁.map (ρe.hom.app y) ≫ σ₁.hom.app (UY.obj y)

variable {Pe : 𝒴 ⥤ 𝒯} {Pg : 𝒯 ⥤ 𝒮} {Ph : 𝒴 ⥤ 𝒳} {Pf : 𝒳 ⥤ 𝒮} {P : 𝒴 ⥤ 𝒮}
  {Pe₁ : 𝒴' ⥤ 𝒯'} {Pg₁ : 𝒯' ⥤ 𝒮'} {Ph₁ : 𝒴' ⥤ 𝒳'} {Pf₁ : 𝒳' ⥤ 𝒮'} {P₁' P' : 𝒴' ⥤ 𝒮'}
  {ρe : Pe ⋙ UT ≅ UY ⋙ Pe₁} {ρg : Pg ⋙ US ≅ UT ⋙ Pg₁} {ρh : Ph ⋙ UX ≅ UY ⋙ Ph₁}
  {ρf : Pf ⋙ US ≅ UX ⋙ Pf₁} {ρ : P ⋙ US ≅ UY ⋙ P'}
  {ψ₁ : P ≅ Pe ⋙ Pg} {ψ₂ : P ≅ Ph ⋙ Pf}
  {c₁ : Pe₁ ⋙ Pg₁ ≅ P₁'} {κ : P₁' ≅ P'} {c₂ : Ph₁ ⋙ Pf₁ ≅ P'}

/-- **A comparison of two factorizations of the same functor transports, piece by piece.** If the
`U`'s carry the factorizations `ψ₁`, `ψ₂` of `P` to `c₁ ≫ κ` and `c₂`, they carry `ψ₁⁻¹ ≫ ψ₂` to
`c₁ ≫ κ ≫ c₂⁻¹`. -/
theorem SquareCompat.of_compCompat (h₁ : CompCompat ρe ρg ρ ψ₁ (c₁ ≪≫ κ))
    (h₂ : CompCompat ρh ρf ρ ψ₂ c₂) :
    SquareCompat ρe ρg ρh ρf (ψ₁.symm ≪≫ ψ₂) (c₁ ≪≫ κ ≪≫ c₂.symm) := by
  intro y
  have h₁' : ρg.hom.app (Pe.obj y) ≫ Pg₁.map (ρe.hom.app y) =
      US.map (ψ₁.inv.app y) ≫ ρ.hom.app y ≫ (c₁ ≪≫ κ).inv.app (UY.obj y) := by
    rw [← h₁ y, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    h₂ y]
  rw [reassoc_of% h₁']
  simp

end Compat

/-! ### Mates -/

section Mate

variable {𝒯 𝒮 𝒳 𝒴 𝒯' 𝒮' 𝒳' 𝒴' : Type*} [Category* 𝒯] [Category* 𝒮] [Category* 𝒳]
  [Category* 𝒴] [Category* 𝒯'] [Category* 𝒮'] [Category* 𝒳'] [Category* 𝒴']
  {UT : 𝒯 ⥤ 𝒯'} {US : 𝒮 ⥤ 𝒮'} {UX : 𝒳 ⥤ 𝒳'} {UY : 𝒴 ⥤ 𝒴'}

/-- **The comparisons `τ : F ⋙ G ⟶ G' ⋙ F'` and `τ₁` correspond under the `U`'s**, through the
commutation isomorphisms of the four edges: the hypothesis of
`Stacks.Cohomology.BaseChange.derived_exactTransport_app`, and the conclusion of
`Stacks.Cohomology.BaseChange.mate_exactTransport_app`. -/
def NatTransCompat {F : 𝒯 ⥤ 𝒮} {G : 𝒮 ⥤ 𝒳} {G' : 𝒯 ⥤ 𝒴} {F' : 𝒴 ⥤ 𝒳} {F₁ : 𝒯' ⥤ 𝒮'}
    {G₁ : 𝒮' ⥤ 𝒳'} {G₁' : 𝒯' ⥤ 𝒴'} {F₁' : 𝒴' ⥤ 𝒳'} (aF : F ⋙ US ≅ UT ⋙ F₁)
    (aF' : F' ⋙ UX ≅ UY ⋙ F₁') (aG : G ⋙ UX ≅ US ⋙ G₁) (aG' : G' ⋙ UY ≅ UT ⋙ G₁')
    (τ : F ⋙ G ⟶ G' ⋙ F') (τ₁ : F₁ ⋙ G₁ ⟶ G₁' ⋙ F₁') : Prop :=
  ∀ t : 𝒯, UX.map (τ.app t) ≫ aF'.hom.app (G'.obj t) ≫ F₁'.map (aG'.hom.app t) =
    aG.hom.app (F.obj t) ≫ G₁.map (aF.hom.app t) ≫ τ₁.app (UT.obj t)

variable {Lf : 𝒮 ⥤ 𝒳} {Pf : 𝒳 ⥤ 𝒮} (adjf : Lf ⊣ Pf) {Le : 𝒯 ⥤ 𝒴} {Pe : 𝒴 ⥤ 𝒯} (adje : Le ⊣ Pe)
  {Lf₁ : 𝒮' ⥤ 𝒳'} {Pf₁ : 𝒳' ⥤ 𝒮'} (adjf₁ : Lf₁ ⊣ Pf₁)
  {Le₁ : 𝒯' ⥤ 𝒴'} {Pe₁ : 𝒴' ⥤ 𝒯'} (adje₁ : Le₁ ⊣ Pe₁)
  {Pg : 𝒯 ⥤ 𝒮} {Ph : 𝒴 ⥤ 𝒳} {Pg₁ : 𝒯' ⥤ 𝒮'} {Ph₁ : 𝒴' ⥤ 𝒳'}
  {σ : Pe ⋙ Pg ≅ Ph ⋙ Pf} {σ₁ : Pe₁ ⋙ Pg₁ ≅ Ph₁ ⋙ Pf₁}
  {ρg : Pg ⋙ US ≅ UT ⋙ Pg₁} {ρh : Ph ⋙ UX ≅ UY ⋙ Ph₁} {ρf : Pf ⋙ US ≅ UX ⋙ Pf₁}
  {ρe : Pe ⋙ UT ≅ UY ⋙ Pe₁} {lf : Lf ⋙ UX ≅ US ⋙ Lf₁} {le : Le ⋙ UY ≅ UT ⋙ Le₁}

/-- `Stacks.Cohomology.BaseChange.mate_exactTransport_app` in terms of `SquareCompat` and
`NatTransCompat`. -/
theorem NatTransCompat.mate
    (hcounit : ∀ x : 𝒳, UX.map (adjf.counit.app x) =
      lf.hom.app (Pf.obj x) ≫ Lf₁.map (ρf.hom.app x) ≫ adjf₁.counit.app (UX.obj x))
    (hunit : ∀ t : 𝒯, UT.map (adje.unit.app t) ≫ ρe.hom.app (Le.obj t) ≫
      Pe₁.map (le.hom.app t) = adje₁.unit.app (UT.obj t))
    (hσ : SquareCompat ρe ρg ρh ρf σ σ₁) :
    NatTransCompat ρg ρh lf le (mate adjf adje Pg Ph σ) (mate adjf₁ adje₁ Pg₁ Ph₁ σ₁) :=
  mate_exactTransport_app adjf adje adjf₁ adje₁ hcounit hunit hσ

end Mate

/-! ### Descents to bounded below derived categories -/

section Derived

-- `Stacks.Cohomology.BaseChange.derived` (`StacksFrontier/Topology/Sheaves/Cohomology/
-- StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean:204`) is built under the standard model.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {T S X Y T' S' X' Y' : Type*} [Category* T] [Category* S] [Category* X] [Category* Y]
  [Category* T'] [Category* S'] [Category* X'] [Category* Y']
  [Abelian T] [Abelian S] [Abelian X] [Abelian Y] [Abelian T'] [Abelian S'] [Abelian X']
  [Abelian Y'] [EnoughInjectives T] [EnoughInjectives S] [EnoughInjectives Y]
  [EnoughInjectives T'] [EnoughInjectives S'] [EnoughInjectives Y']
  {F : T ⥤ S} {F' : Y ⥤ X} {G : S ⥤ X} {G' : T ⥤ Y}
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  {F₁ : T' ⥤ S'} {F₁' : Y' ⥤ X'} {G₁ : S' ⥤ X'} {G₁' : T' ⥤ Y'}
  [F₁.Additive] [F₁'.Additive] [G₁.Additive] [G₁'.Additive]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  {UT : T ⥤ T'} {US : S ⥤ S'} {UX : X ⥤ X'} {UY : Y ⥤ Y'}
  [UT.Additive] [PreservesFiniteLimits UT] [PreservesFiniteColimits UT]
  [US.Additive] [PreservesFiniteLimits US] [PreservesFiniteColimits US]
  [UX.Additive] [PreservesFiniteLimits UX] [PreservesFiniteColimits UX]
  [UY.Additive] [PreservesFiniteLimits UY] [PreservesFiniteColimits UY]
  {aF : F ⋙ US ≅ UT ⋙ F₁} {aF' : F' ⋙ UX ≅ UY ⋙ F₁'}
  {aG : G ⋙ UX ≅ US ⋙ G₁} {aG' : G' ⋙ UY ≅ UT ⋙ G₁'}
  {τ : F ⋙ G ⟶ G' ⋙ F'} {τ₁ : F₁ ⋙ G₁ ⟶ G₁' ⋙ F₁'}

/-- **The descended comparisons are invertible together.** If `τ` and `τ₁` correspond under the
`U`'s and `U_X` reflects isomorphisms on `D⁺`, then the descent of `τ` is invertible at `M`
exactly when the descent of `τ₁` is invertible at `U_T(M)`: by
`Stacks.Cohomology.BaseChange.derived_exactTransport_app` the two differ by the commutation
isomorphisms of the right derived functors with the `U`'s. -/
theorem isIso_derived_app_iff_of_natTransCompat
    (hF : ∀ I : T, Injective I → F₁.rightAcyclic (UT.obj I))
    (hF' : ∀ I : Y, Injective I → F₁'.rightAcyclic (UY.obj I))
    (hG : ∀ I : S, Injective I → G₁.rightAcyclic (US.obj I))
    (hG' : ∀ I : T, Injective I → G₁'.rightAcyclic (UT.obj I))
    (hτ : NatTransCompat aF aF' aG aG' τ τ₁) [UX.mapDerivedCategoryPlus.ReflectsIsomorphisms]
    (M : DerivedCategory.Plus T) :
    IsIso ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app M) ↔
      IsIso ((derived F₁ F₁' G₁ G₁' τ₁ (asIso G₁.rightDerivedFunctorPlusUnith)).app
        (UT.mapDerivedCategoryPlus.obj M)) := by
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff, isIso_iff_of_reflects_iso] using
    (congrArg IsIso (derived_exactTransport_app hF hF' hG hG' hτ M)).to_iff

end Derived

end Stacks.Cohomology.BaseChange

end
