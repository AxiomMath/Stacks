module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtProjectionFormulaBaseChange

/-!
# The coefficient complexes of Stacks 08JR after base change, on the preimage neighbourhood

For a cartesian square `X' = X ×_Y Y'` and the quasi-compact neighbourhood `V` of the support of
`𝒢^•` used in the proof of Stacks 08JR, this file moves `Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*N)`
to the preimage `g'⁻¹V` and to a perfect approximation of `E|_V`.

## Main definitions

* `AlgebraicGeometry.Space.edsRestrictPullbackComplexIso`.
* `AlgebraicGeometry.Space.tensorPullbackComplexIsoOfIso`.
* `AlgebraicGeometry.Space.baseChangeRestrictApproximationExt`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive preservesFiniteLimits_etaleModulePullback
  preservesFiniteColimits_etaleModulePullback

attribute [local instance] smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over
  hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X X' : AlgebraicSpaces B S hS}

variable {Uo : Subfunctor X.1} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 Uo V.ι) (g' : X' ⟶ X)
  {Uo' : Subfunctor X'.1}
  (hsq' : IsElementaryDistinguishedSquare B S hS X'.2 Uo' (V.preimage g'.hom).ι)

/-- **The restriction of `(g')^*𝒢^•` to the preimage neighbourhood** is the pullback of `𝒢^•|_V`
along `g'⁻¹V ⟶ V`, both being pullbacks along `g'⁻¹V ⟶ X`. -/
def edsRestrictPullbackComplexIso
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ) :
    (pullbackComplexSmallEtale (edsEtaleHom B S hS hsq')).obj
        ((pullbackComplexSmallEtale g').obj G) ≅
      (pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) :=
  (Functor.mapHomologicalComplexCompIso
      (pullbackModulesCompSmallEtaleIso (edsEtaleHom B S hS hsq') g') (ComplexShape.up ℤ)).app G ≪≫
    eqToIso (congrArg (fun φ => (pullbackComplexSmallEtale φ).obj G)
      (isPullback_edsEtalePreimageHom hsq g' hsq').w.symm) ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (pullbackModulesCompSmallEtaleIso (edsEtalePreimageHom hsq g' hsq')
        (edsEtaleHom B S hS hsq)) (ComplexShape.up ℤ)).app G).symm

variable {Y Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}

/-- `𝒢^• ⊗ f^*-` along an isomorphism of the complexes `𝒢^•`. -/
def tensorPullbackComplexIsoOfIso {Z W : AlgebraicSpaces B S hS} (h : Z ⟶ W)
    {G₁ G₂ : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ}
    (e : G₁ ≅ G₂) : tensorPullbackComplex h G₁ ≅ tensorPullbackComplex h G₂ :=
  Functor.isoWhiskerLeft (pullbackComplexSmallEtale h)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (smallEtaleRingedTopos B S hS Z).O).map₂HomologicalComplex (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)).mapIso e)

/-- An object of the derived category of `𝒪_X`-modules in the spelling
`SheafOfModules (ringedToposStructureRingSheaf X)` of derived pullback, read in the spelling
`Modules X.1 X.2` of the restriction lemmas. The two spellings are definitionally equal, but
instance resolution, which works up to reducible transparency, does not identify them. -/
abbrev asModulesObj (Z : AlgebraicSpaces B S hS)
    (A : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))) :
    DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2) :=
  A

/-- **The `Ext` groups of the base change, moved to the preimage neighbourhood and to a perfect
approximation.** Let `c : P ⟶ E|_V` be an isomorphism on `Hʲ` for `j > s`. For a complex `N` of
`𝒪_{Y'}`-modules such that `(g')^*𝒢^• ⊗ (f')^*N` is supported on the closed complement of the open
member of the square of `X'`, and such that its restriction to `g'⁻¹V` lies in degrees `≥ a`,
and `i + s + 2 ≤ a`,
`Ext^i_{X'}(L(g')^*E, (g')^*𝒢^• ⊗ (f')^*N) ≅ Ext^i_{g'⁻¹V}(L(g'|)^*P, (g'|)^*(𝒢^•|_V) ⊗ (f'|)^*N)`:
the restriction of Stacks 08GG, restriction commuting with derived pullback, and the
insensitivity of `Ext` into bounded below objects to `L(g'|)^*c`. -/
def baseChangeRestrictApproximationExt
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (c : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) (s : ℤ)
    (hc : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')) ℤ)
    (hN : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N))
    (a : ℤ) (ha : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)) N).IsGE a)
    (i : ℤ) (hi : i + s + 2 ≤ a) :
    (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
        (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N)⟦i⟧) ≃+
      (asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
          (edsEtalePreimageHom hsq g' hsq')).obj P) ⟶
        (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
          ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
            ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)) N)⟦i⟧) :=
  (edsRestrictCoefficientExt hsq' f' ((pullbackComplexSmallEtale g').obj G)
      (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E)) N hN i).trans <|
  (homAddEquivOfIsoSource (C := DerivedCategory (Modules.{u, u} B S hS
      (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2))
    (show (edsEtaleRestrict B S hS hsq').obj
          (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E)) ≅
        asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
          (edsEtalePreimageHom hsq g' hsq')).obj ((edsEtaleRestrict B S hS hsq).obj E)) from
      edsEtaleRestrictDerivedPullbackIso hsq g' hsq' E) _).trans <|
  (homAddEquivOfIsoTarget (C := DerivedCategory (Modules.{u, u} B S hS
      (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) _
    ((shiftFunctor _ i).mapIso (DerivedCategory.Q.mapIso
      ((tensorPullbackComplexIsoOfIso (edsEtaleHom B S hS hsq' ≫ f')
        (edsRestrictPullbackComplexIso hsq g' hsq' G)).app N)))).trans <|
  AddEquiv.ofBijective (Preadditive.leftComp (C := DerivedCategory (Modules.{u, u} B S hS
      (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) _
      (show asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).obj P) ⟶
          asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).obj ((edsEtaleRestrict B S hS hsq).obj E)) from
        (smallEtaleDerivedModulePullback B S hS (edsEtalePreimageHom hsq g' hsq')).map c))
    (by
      have := ha
      exact bijective_comp_smallEtaleDerivedModulePullback_shiftedHom _ c s hc _ a i hi)

/-- Reassociating `lc ≫ ((ρ ≫ ex') ≫ κ')` along `ex' = ex ≫ ψ'` and `ψ' ≫ κ' = κ ≫ ψV`; stated for
an arbitrary category, so that using it does not unfold the morphisms it is applied to. -/
theorem reassoc_comp_of_eq_comp_of_comm {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : C}
    (lc : A₀ ⟶ A₁) (ρ : A₁ ⟶ A₂) (ex : A₂ ⟶ A₃) (ex' : A₂ ⟶ A₄) (ψ' : A₃ ⟶ A₄) (κ' : A₄ ⟶ A₆)
    (κ : A₃ ⟶ A₅) (ψV : A₅ ⟶ A₆) (he : ex' = ex ≫ ψ') (hc : ψ' ≫ κ' = κ ≫ ψV) :
    lc ≫ ((ρ ≫ ex') ≫ κ') = (lc ≫ ((ρ ≫ ex) ≫ κ)) ≫ ψV := by
  rw [he]
  simp only [Category.assoc, hc]

/-- Moving three morphisms past each other along three commutative squares, stated for an arbitrary
category, so that using it does not unfold the morphisms it is applied to. -/
theorem comp_comp_comp_eq_of_comm₃ {C : Type*} [Category C] {A₀ A₁ A₂ A₃ A₄ B₁ B₂ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ A₃} {r : A₃ ⟶ A₄} {x : A₀ ⟶ B₁} {y : B₁ ⟶ A₂}
    {z : B₁ ⟶ B₂} {w : B₂ ⟶ A₃} {r' : B₂ ⟶ A₄} (h₁ : a ≫ b = x ≫ y) (h₂ : y ≫ c = z ≫ w)
    (h₃ : w ≫ r = r') : a ≫ b ≫ c ≫ r = x ≫ z ≫ r' := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

/-- Moving a morphism past two morphisms along two commutative squares, stated for an arbitrary
category, so that using it does not unfold the morphisms it is applied to. -/
theorem comp_comp_eq_of_comm₂ {C : Type*} [Category C] {A₀ A₁ A₂ B₁ B₂ B₃ : C}
    {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂} {c : A₂ ⟶ B₃} {x : A₀ ⟶ B₁} {y : B₁ ⟶ A₂} {z : B₁ ⟶ B₂}
    {w : B₂ ⟶ B₃} (h₁ : a ≫ b = x ≫ y) (h₂ : y ≫ c = z ≫ w) :
    a ≫ (b ≫ c) = (x ≫ z) ≫ w := by
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- Composing an equation `a = x ≫ y` with a commutative square `y ≫ c = z ≫ w`, stated for an
arbitrary category, so that using it does not unfold the morphisms it is applied to. -/
theorem comp_eq_of_eq_comp_of_comm {C : Type*} [Category C] {A₀ A₁ A₂ B₁ B₂ : C}
    {a : A₀ ⟶ A₁} {c : A₁ ⟶ A₂} {x : A₀ ⟶ B₁} {y : B₁ ⟶ A₁} {z : B₁ ⟶ B₂} {w : B₂ ⟶ A₂}
    (h₁ : a = x ≫ y) (h₂ : y ≫ c = z ≫ w) : a ≫ c = (x ≫ z) ≫ w := by
  rw [h₁, Category.assoc, h₂, Category.assoc]

attribute [local irreducible] edsRestrictCoefficientExtHom edsEtaleRestrictDerivedPullbackIso
  tensorPullbackComplexIsoOfIso edsRestrictPullbackComplexIso in
/-- `baseChangeRestrictApproximationExt`, unfolded. -/
theorem baseChangeRestrictApproximationExt_apply
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (c : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) (s : ℤ)
    (hc : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    (N : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')) ℤ)
    (hN : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N))
    (a : ℤ) (ha : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)) N).IsGE a)
    (i : ℤ) (hi : i + s + 2 ≤ a)
    (x : asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
        (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N)⟦i⟧) :
    baseChangeRestrictApproximationExt hsq g' hsq' G E P c s hc N hN a ha i hi x =
      (show asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).obj P) ⟶
          asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).obj ((edsEtaleRestrict B S hS hsq).obj E)) from
        (smallEtaleDerivedModulePullback B S hS (edsEtalePreimageHom hsq g' hsq')).map c) ≫
        ((show asModulesObj _ ((smallEtaleDerivedModulePullback B S hS
            (edsEtalePreimageHom hsq g' hsq')).obj ((edsEtaleRestrict B S hS hsq).obj E)) ⟶
              (edsEtaleRestrict B S hS hsq').obj
                (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E)) from
            (edsEtaleRestrictDerivedPullbackIso hsq g' hsq' E).inv) ≫
          edsRestrictCoefficientExtHom hsq' f' ((pullbackComplexSmallEtale g').obj G)
            (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E)) N i x) ≫
        (shiftFunctor (DerivedCategory (Modules.{u, u} B S hS
          (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) i).map (DerivedCategory.Q.map
            ((tensorPullbackComplexIsoOfIso (edsEtaleHom B S hS hsq' ≫ f')
              (edsRestrictPullbackComplexIso hsq g' hsq' G)).hom.app N)) :=
  rfl

/-- **`baseChangeRestrictApproximationExt` is natural in the coefficient complex `N`.** -/
theorem baseChangeRestrictApproximationExt_naturality
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (P : DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq))))
    (c : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) (s : ℤ)
    (hc : ∀ j : ℤ, s < j → IsIso ((DerivedCategory.homologyFunctor _ j).map c))
    {N N' : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y')) ℤ}
    (q : N ⟶ N')
    (hN : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N))
    (hN' : CohomologySupportedOn B S hS X'.1 X'.2 (edsComplementPoints B S hS Uo')
      (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N'))
    (a : ℤ) (ha : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)) N).IsGE a)
    (ha' : (show DerivedCategory (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS (edsEtale B S hS hsq'))) from
      tensorPullbackComplexDerived (edsEtaleHom B S hS hsq' ≫ f')
      ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)) N').IsGE a)
    (i : ℤ) (hi : i + s + 2 ≤ a)
    (x : asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E) ⟶
        (tensorPullbackComplexDerived f' ((pullbackComplexSmallEtale g').obj G) N)⟦i⟧) :
    baseChangeRestrictApproximationExt hsq g' hsq' G E P c s hc N' hN' a ha' i hi
        (x ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f'
          ((pullbackComplexSmallEtale g').obj G)).map q))⟦i⟧') =
      baseChangeRestrictApproximationExt hsq g' hsq' G E P c s hc N hN a ha i hi x ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq' ≫ f')
          ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
            ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).map q))⟦i⟧' := by
  have h1 := edsRestrictCoefficientExtHom_naturality hsq' f' ((pullbackComplexSmallEtale g').obj G)
    (asModulesObj X' ((smallEtaleDerivedModulePullback B S hS g').obj E)) q i x
  let κ := tensorPullbackComplexIsoOfIso (edsEtaleHom B S hS hsq' ≫ f')
    (edsRestrictPullbackComplexIso hsq g' hsq' G)
  let Sh := shiftFunctor (DerivedCategory (Modules.{u, u} B S hS
    (edsEtale B S hS hsq').1 (edsEtale B S hS hsq').2)) i
  have h2 : Sh.map (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq' ≫ f')
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq')).obj
          ((pullbackComplexSmallEtale g').obj G))).map q)) ≫
        Sh.map (DerivedCategory.Q.map (κ.hom.app N')) =
      Sh.map (DerivedCategory.Q.map (κ.hom.app N)) ≫
        Sh.map (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq' ≫ f')
          ((pullbackComplexSmallEtale (edsEtalePreimageHom hsq g' hsq')).obj
            ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).map q)) :=
    (Sh.map_comp _ _).symm.trans ((congrArg Sh.map ((DerivedCategory.Q.map_comp _ _).symm.trans
      ((congrArg DerivedCategory.Q.map (κ.hom.naturality q)).trans
        (DerivedCategory.Q.map_comp _ _)))).trans (Sh.map_comp _ _))
  refine (baseChangeRestrictApproximationExt_apply hsq g' hsq' G E P c s hc N' hN' a ha' i hi
    _).trans ((reassoc_comp_of_eq_comp_of_comm _ _ _ _ _ _ _ _ h1 h2).trans ?_)
  exact congrArg (· ≫ _)
    (baseChangeRestrictApproximationExt_apply hsq g' hsq' G E P c s hc N hN a ha i hi x).symm

end AlgebraicGeometry.Space

end
