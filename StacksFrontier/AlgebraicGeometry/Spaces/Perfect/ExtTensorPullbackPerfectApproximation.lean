module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtPerfectDualTowerData
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ExtRepresentingTower
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleTensorCohomology

/-!
# Stacks 08JR, part (A)

Let `Y` be a Noetherian algebraic space, `f : X ⟶ Y` locally of finite type and quasi-separated,
`E ∈ D^-_{Coh}(𝒪_X)` and `𝒢^•` a bounded complex of coherent `𝒪_X`-modules, flat over `Y`, with
support proper over `Y`.  For every `m` there are a perfect `K ∈ D(𝒪_Y)` and maps
`α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢^• ⊗ f^*ℱ) ⟶ H^i(Y, K ⊗^L ℱ)` for quasi-coherent `ℱ`, functorial in `ℱ`,
compatible with the boundary maps, and invertible for `i ≤ m`.

Following the proof of Stacks 08JR (A): restrict to a quasi-compact open neighbourhood `V` of the
support of `𝒢^•` (a Noetherian algebraic space; restriction is bijective on these `Ext` groups,
Stacks 08GG), choose a perfect `P ⟶ E|_V` inducing bijections `Ext^i(E|_V, M) ⟶ Ext^i(P, M)` for
`i ≤ m` and `M ≥ a` (Stacks 08HP and 06XS, `𝒢ⁿ = 0` for `n < a`), and apply Stacks 08JN to `P`
with `K = R(f|_V)_* RSheafHom(P, 𝒢^•|_V)`.

## Main results

* `AlgebraicGeometry.Space.exists_isPerfect_tensorPullbackExtGroup_smallEtaleTensorCohomology`:
  Stacks 08JR (A).

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/-- A square `f₁ ≫ g' = g ≫ y` and an isomorphism of squares `m ≫ e'.hom = e.hom ≫ y` give
`f₁ ≫ g' ≫ e'.inv = (g ≫ e.inv) ≫ m`. -/
theorem CategoryTheory.comp_comp_inv_eq_comp_inv_comp_of_comm {C : Type*} [Category* C]
    {A A' B B' D D' : C} {f₁ : A ⟶ A'} {g : A ⟶ B} {g' : A' ⟶ B'} {y : B ⟶ B'} {e : D ≅ B}
    {e' : D' ≅ B'} {m : D ⟶ D'} (hg : f₁ ≫ g' = g ≫ y) (hc : m ≫ e'.hom = e.hom ≫ y) :
    f₁ ≫ g' ≫ e'.inv = (g ≫ e.inv) ≫ m := by
  have h : e.inv ≫ m = y ≫ e'.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact hc
  rw [Category.assoc, h, ← Category.assoc g, ← hg, Category.assoc]

/-- **A square of `Hom` groups followed by isomorphisms of abelian groups.**  Let
`φ : Hom(X, M) → Hom(Y, N)` and `φ' : Hom(X, M') → Hom(Y, N')` be additive and commute with
composition with `h : M ⟶ M'` and `h' : N ⟶ N'`, and let `c : H ≅ Hom(Y, N)`,
`c' : H' ≅ Hom(Y, N')` be isomorphisms with `m ≫ c' = c ≫ (- ≫ h')`.  Then `φ ≫ c⁻¹` and
`φ' ≫ c'⁻¹` commute with `(- ≫ h)` and `m`. -/
theorem CategoryTheory.preadditiveCoyoneda_map_comp_ofHom_mk'_comp_inv.{v, u₁, u₂}
    {C : Type u₁} {D : Type u₂} [Category.{v} C] [Preadditive C] [Category.{v} D] [Preadditive D]
    {X M M' : C} {Y N N' : D} {H H' : AddCommGrpCat.{v}} (h : M ⟶ M') (h' : N ⟶ N') (m : H ⟶ H')
    (φ : (X ⟶ M) → (Y ⟶ N)) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (φ' : (X ⟶ M') → (Y ⟶ N')) (hφ' : ∀ a b, φ' (a + b) = φ' a + φ' b)
    (c : H ≅ (preadditiveCoyoneda.obj (Opposite.op Y)).obj N)
    (c' : H' ≅ (preadditiveCoyoneda.obj (Opposite.op Y)).obj N')
    (hψ : ∀ e : X ⟶ M, φ' (e ≫ h) = φ e ≫ h')
    (hc : m ≫ c'.hom = c.hom ≫ (preadditiveCoyoneda.obj (Opposite.op Y)).map h') :
    (preadditiveCoyoneda.obj (Opposite.op X)).map h ≫
        (AddCommGrpCat.ofHom (AddMonoidHom.mk' φ' hφ') ≫ c'.inv) =
      (AddCommGrpCat.ofHom (AddMonoidHom.mk' φ hφ) ≫ c.inv) ≫ m :=
  CategoryTheory.comp_comp_inv_eq_comp_inv_comp_of_comm
    (AddCommGrpCat.ext fun e => by exact hψ e) hc

/-- The morphism of abelian groups of a bijective additive map is an isomorphism. -/
theorem AddCommGrpCat.isIso_ofHom_mk'_of_bijective.{v} {A B : Type v} [AddCommGroup A]
    [AddCommGroup B] (φ : A → B) (hφ : ∀ a b, φ (a + b) = φ a + φ b) (hb : Function.Bijective φ) :
    IsIso (AddCommGrpCat.ofHom (AddMonoidHom.mk' φ hφ)) :=
  (ConcreteCategory.isIso_iff_bijective _).2 hb

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-! ### The groups `Ext^i_{𝒪_X}(E, 𝒢^• ⊗ f^*ℱ)` -/

/-- **The group `Ext^i_{𝒪_X}(E, 𝒢^• ⊗ f^*ℱ) = Hom(E, (𝒢^• ⊗ f^*ℱ)[i])`**, for an `𝒪_Y`-module `ℱ`
placed in degree `0`. -/
abbrev tensorPullbackExtGroup (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ) :
    AddCommGrpCat.{u + 1} :=
  (preadditiveCoyoneda.obj (op E)).obj ((tensorPullbackComplexDerived f G
    ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F))⟦i⟧)

/-- **The map `Ext^i(E, 𝒢^• ⊗ f^*ℱ) ⟶ Ext^i(E, 𝒢^• ⊗ f^*ℱ')` induced by `ℱ ⟶ ℱ'`.** -/
abbrev tensorPullbackExtGroupMap (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ) :
    tensorPullbackExtGroup B S hS E f G F i ⟶ tensorPullbackExtGroup B S hS E f G F' i :=
  (preadditiveCoyoneda.obj (op E)).map ((DerivedCategory.Q.map ((tensorPullbackComplex f G).map
    ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).map q)))⟦i⟧')

/-- **The boundary map `Ext^i(E, 𝒢^• ⊗ f^*ℱ₃) ⟶ Ext^{i+1}(E, 𝒢^• ⊗ f^*ℱ₁)`** of a short exact
sequence `0 ⟶ 𝒢^• ⊗ f^*ℱ₁ ⟶ 𝒢^• ⊗ f^*ℱ₂ ⟶ 𝒢^• ⊗ f^*ℱ₃ ⟶ 0` of complexes (the image of
`ℱ₁[0] ⟶ ℱ₂[0] ⟶ ℱ₃[0]` under `𝒢^• ⊗ f^*(-)`): composition with the boundary map of its
distinguished triangle in `D(𝒪_X)`. -/
abbrev tensorPullbackExtGroupDelta (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : ((ShortComplex.mk ((HomologicalComplex.single (SheafOfModules.{u}
        (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
          (tensorPullbackComplex f G)).ShortExact)
    (i j : ℤ) (h : i + 1 = j) :
    tensorPullbackExtGroup B S hS E f G T.X₃ i ⟶ tensorPullbackExtGroup B S hS E f G T.X₁ j :=
  (preadditiveCoyoneda.obj (op E)).map ((DerivedCategory.triangleOfSESδ hT)⟦i⟧' ≫
    (shiftFunctorAdd' _ 1 i j (by omega)).inv.app (tensorPullbackComplexDerived f G
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₁)))

/-! ### Restriction to `V` followed by a perfect approximation -/

section Approximation

variable {Z : Set (points B S hS X.1)} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
  (f : X ⟶ Y) (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
  (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))

/-- `x ≫ (𝒢^•|_V ⊗ f|_V^*q)[i]` for `x : E|_V ⟶ (𝒢^•|_V ⊗ f|_V^*ℱ)[i]`, read in the two spellings
of `D(𝒪_V)`. -/
theorem comp_extPerfectCoefficientMap_shift_eq
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ)
    (x : ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
      (edsEtale B S hS hsq)) ⟶
        (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) F)⟦i⟧) :
    (x ≫ (extPerfectCoefficientMap B S hS (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) q)⟦i⟧' :
        ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) ⟶ _) =
      ((x : (edsEtaleRestrict B S hS hsq).obj E ⟶
          (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
            ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F))⟦i⟧) ≫
        (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).map q)))⟦i⟧' :) :=
  rfl

/-- `x` followed by the boundary map of `𝒢^•|_V ⊗ f|_V^*(-)` of a short exact sequence, read in the
two spellings of `D(𝒪_V)`. -/
theorem shiftedHom_comp_extPerfectCoefficientDelta_eq
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT' : ((T.map (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact) (i : ℤ)
    (x : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
      (edsEtale B S hS hsq))
      (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T.X₃) i) :
    (x.comp (extPerfectCoefficientDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T hT') (add_comm 1 i) :
        ((edsEtaleRestrict B S hS hsq).obj E : smallEtaleModulesDerived B S hS
          (edsEtale B S hS hsq)) ⟶ _) =
      (ShiftedHom.comp (C := DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
          (edsEtale B S hS hsq).2)) (X := (edsEtaleRestrict B S hS hsq).obj E)
        (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).obj T.X₃)) x
        (DerivedCategory.triangleOfSESδ (S := (ShortComplex.mk
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).map T.f) ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map
          T.g)
          (single_map_comp_map_eq_zero B S hS T)).map (tensorPullbackComplex
            (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj
            G))) hT')
        (add_comm 1 i) :) :=
  rfl

/-- The restriction `E|_V`, as an object of `D(𝒪_V)` in the spelling
`AlgebraicGeometry.Space.smallEtaleModulesDerived`. -/
abbrev edsEtaleRestrictSmallEtale : smallEtaleModulesDerived B S hS (edsEtale B S hS hsq) :=
  (edsEtaleRestrict B S hS hsq).obj E

/-- The sum of two morphisms `E|_V ⟶ (𝒢^•|_V ⊗ f|_V^*ℱ)[i]`, read in the two spellings of
`D(𝒪_V)`. -/
theorem edsEtaleRestrictSmallEtale_hom_add
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ)
      (a b : (edsEtaleRestrict B S hS hsq).obj E ⟶ (tensorPullbackComplexDerived
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F))⟦i⟧) :
    ((a + b : (edsEtaleRestrict B S hS hsq).obj E ⟶ (tensorPullbackComplexDerived
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F))⟦i⟧) : edsEtaleRestrictSmallEtale B S hS hsq E ⟶
      (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) F)⟦i⟧) =
      (a : edsEtaleRestrictSmallEtale B S hS hsq E ⟶ (extPerfectCoefficientObj B S hS
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
      F)⟦i⟧) + (b : edsEtaleRestrictSmallEtale B S hS hsq E ⟶
      (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) F)⟦i⟧) :=
  rfl

/-- A morphism `E|_V ⟶ (𝒢^•|_V ⊗ f|_V^*ℱ)[i]` of `D(𝒪_V)`, read in the spelling
`AlgebraicGeometry.Space.smallEtaleModulesDerived`. -/
abbrev edsRestrictSmallEtaleCast (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (i : ℤ) (x : (edsEtaleRestrict B S hS hsq).obj E ⟶
      (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F))⟦i⟧) :
    edsEtaleRestrictSmallEtale B S hS hsq E ⟶ (extPerfectCoefficientObj B S hS
      (edsEtaleHom B S hS hsq ≫ f) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
      F)⟦i⟧ :=
  x

/-- `AlgebraicGeometry.Space.edsRestrictSmallEtaleCast` is additive. -/
theorem edsRestrictSmallEtaleCast_add
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ)
    (a b : (edsEtaleRestrict B S hS hsq).obj E ⟶
      (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F))⟦i⟧) :
    edsRestrictSmallEtaleCast B S hS hsq f G E F i (a + b) =
      edsRestrictSmallEtaleCast B S hS hsq f G E F i a +
        edsRestrictSmallEtaleCast B S hS hsq f G E F i b :=
  rfl

/-- `AlgebraicGeometry.Space.edsRestrictSmallEtaleCast` commutes with postcomposition by the map
induced by a morphism `ℱ ⟶ ℱ'`. -/
theorem edsRestrictSmallEtaleCast_comp_map
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ)
    (x : (edsEtaleRestrict B S hS hsq).obj E ⟶
      (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F))⟦i⟧) :
    edsRestrictSmallEtaleCast B S hS hsq f G E F' i
        (x ≫ (DerivedCategory.Q.map ((tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)).map
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).map q)))⟦i⟧') =
      edsRestrictSmallEtaleCast B S hS hsq f G E F i x ≫
        (extPerfectCoefficientMap B S hS (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) q)⟦i⟧' :=
  rfl

/-- `AlgebraicGeometry.Space.edsRestrictSmallEtaleCast` commutes with composition with the
boundary map of a short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0`. -/
theorem edsRestrictSmallEtaleCast_comp_delta
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT' : ((T.map (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact) (i : ℤ)
    (x : ShiftedHom ((edsEtaleRestrict B S hS hsq).obj E)
      (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj T.X₃)) i) :
    edsRestrictSmallEtaleCast B S hS hsq f G E T.X₁ (i + 1)
        (ShiftedHom.comp (Y := tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
          ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
          (ComplexShape.up ℤ) 0).obj T.X₃)) x
          (DerivedCategory.triangleOfSESδ (S := (ShortComplex.mk
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
            ((HomologicalComplex.single (SheafOfModules.{u}
            (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.g)
            (single_map_comp_map_eq_zero B S hS T)).map
              (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))) hT')
          (add_comm 1 i)) =
      ShiftedHom.comp (edsRestrictSmallEtaleCast B S hS hsq f G E T.X₃ i x)
        (extPerfectCoefficientDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T hT') (add_comm 1 i) :=
  rfl

/-- `AlgebraicGeometry.Space.edsRestrictSmallEtaleCast` is bijective. -/
theorem bijective_edsRestrictSmallEtaleCast
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ) :
    Function.Bijective (edsRestrictSmallEtaleCast B S hS hsq f G E F i) :=
  ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩

variable {P : smallEtaleModulesDerived B S hS (edsEtale B S hS hsq)}
  (αP : P ⟶ edsEtaleRestrictSmallEtale B S hS hsq E)

/-- Restriction to `V` followed by composition with `αP`,
`Ext^i_X(E, 𝒢^• ⊗ f^*ℱ) ⟶ Ext^i_V(P, 𝒢^•|_V ⊗ f|_V^*ℱ)`, is additive. -/
theorem edsApproxExt_add (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (i : ℤ) (a b : E ⟶ (tensorPullbackComplexDerived f G
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F))⟦i⟧) :
    (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F i
      (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F) i
      (a + b))) =
      (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F i
        (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)
        i a)) + (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F i
        (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)
        i b)) :=
  (congrArg (αP ≫ ·) ((congrArg (edsRestrictSmallEtaleCast B S hS hsq f G E F i)
    ((edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)
      i).map_add a b)).trans
      (edsRestrictSmallEtaleCast_add B S hS hsq f G E F i _ _))).trans
    (Preadditive.comp_add _ _ _ _ _ _)

/-- Restriction to `V` followed by composition with `αP`,
`Ext^i_X(E, 𝒢^• ⊗ f^*ℱ) ⟶ Ext^i_V(P, 𝒢^•|_V ⊗ f|_V^*ℱ)`, is natural in `ℱ`. -/
theorem edsApproxExt_naturality
    {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)} (q : F ⟶ F') (i : ℤ)
    (e : E ⟶ (tensorPullbackComplexDerived f G ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
      F))⟦i⟧) :
    (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F' i
      (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F') i
      (e ≫ (DerivedCategory.Q.map ((tensorPullbackComplex f G).map
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).map q)))⟦i⟧'))) =
      (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F i
        (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F)
        i e)) ≫
        (extPerfectCoefficientMap B S hS (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) q)⟦i⟧' := by
  rw [edsRestrictCoefficientExtHom_naturality, edsRestrictSmallEtaleCast_comp_map,
    Category.assoc]

/-- Restriction to `V` followed by composition with `αP`,
`Ext^i_X(E, 𝒢^• ⊗ f^*ℱ) ⟶ Ext^i_V(P, 𝒢^•|_V ⊗ f|_V^*ℱ)`, is compatible with the boundary maps. -/
theorem edsApproxExt_delta
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : ((ShortComplex.mk ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hT' : ((T.map (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact) (i : ℤ)
    (e : ShiftedHom E (tensorPullbackComplexDerived f G
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj T.X₃)) i) :
    (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E T.X₁ (i + 1)
      (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj T.X₁)
      (i + 1) (e.comp (DerivedCategory.triangleOfSESδ hT) (add_comm 1 i)))) =
      ShiftedHom.comp ((αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E T.X₃ i
        (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
        T.X₃) i e)))
        (extPerfectCoefficientDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T hT') (add_comm 1 i) := by
  rw [edsRestrictCoefficientExtHom_comp_triangleOfSESδ_mk hsq f G E _ _
    (single_map_comp_map_eq_zero B S hS T) hT hT' i e]
  exact (congrArg (αP ≫ ·)
    (edsRestrictSmallEtaleCast_comp_delta B S hS hsq f G E T hT' i _)).trans
    (Category.assoc _ _ _).symm

/-- Restriction to `V` followed by composition with `αP`,
`Ext^i_X(E, 𝒢^• ⊗ f^*ℱ) ⟶ Ext^i_V(P, 𝒢^•|_V ⊗ f|_V^*ℱ)`, is bijective when the coefficient complex
is supported in the complement of `X ∖ Z` (so that restriction to `V` is bijective, Stacks 08GG)
and composition with `αP` is bijective. -/
theorem bijective_edsApproxExt
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
    (hN : CohomologySupportedOn B S hS X.1 X.2
      (edsComplementPoints B S hS (openSubspaceOfPoints B S hS X.1 Zᶜ))
      (tensorPullbackComplexDerived f G ((HomologicalComplex.single
        (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
        F))) (i : ℤ)
    (hb : Function.Bijective (fun e : edsEtaleRestrictSmallEtale B S hS hsq E ⟶
      (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) F)⟦i⟧ => αP ≫ e)) :
    Function.Bijective (fun e : E ⟶ (tensorPullbackComplexDerived f G
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F))⟦i⟧ => (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F i
      (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F) i
      e))) :=
  hb.comp ((bijective_edsRestrictSmallEtaleCast B S hS hsq f G E F i).comp
    (bijective_edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj F) hN
      i))

/-- `AlgebraicGeometry.Space.edsApproxExt_delta` with `ShiftedHom.comp` written out. -/
theorem edsApproxExt_delta_shift
    (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
    (hT : ((ShortComplex.mk ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).map T.f)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).map T.g) (single_map_comp_map_eq_zero B S hS T)).map
          (tensorPullbackComplex f G)).ShortExact)
    (hT' : ((T.map (HomologicalComplex.single (SheafOfModules.{u}
      (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0)).map
      (tensorPullbackComplex (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G))).ShortExact) (i : ℤ)
    (e : E ⟶ (tensorPullbackComplexDerived f G ((HomologicalComplex.single
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
      T.X₃))⟦i⟧) :
    (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E T.X₁ (i + 1)
        (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
          (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
          T.X₁) (i + 1)
          (e ≫ (DerivedCategory.triangleOfSESδ hT)⟦i⟧' ≫
            (shiftFunctorAdd' _ 1 i (i + 1) (add_comm 1 i)).inv.app
              (tensorPullbackComplexDerived f G ((HomologicalComplex.single
                (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ)
                0).obj T.X₁))))) =
      (αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E T.X₃ i
          (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
            T.X₃) i e)) ≫
        (extPerfectCoefficientDelta B S hS (edsEtaleHom B S hS hsq ≫ f)
          ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T hT')⟦i⟧' ≫
          (shiftFunctorAdd' _ 1 i (i + 1) (add_comm 1 i)).inv.app
            (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
              ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) T.X₁) := by
  have h := edsApproxExt_delta B S hS hsq f G E αP T hT hT' i e
  unfold ShiftedHom.comp at h
  exact h

end Approximation

/-! ### The perfect approximation in the spelling of Stacks 08JN -/

section Spelling

variable {Z : Set (points B S hS X.1)} {V : Subfunctor X.1}
  (hsq : IsElementaryDistinguishedSquare B S hS X.2 (openSubspaceOfPoints B S hS X.1 Zᶜ) V.ι)
  (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))

/-- An object of `D(𝒪_V)` in the spelling `AlgebraicGeometry.Space.Modules`, read in the spelling
`AlgebraicGeometry.Space.smallEtaleModulesDerived`. -/
abbrev edsSmallEtaleObj
    (P : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)) :
    smallEtaleModulesDerived B S hS (edsEtale B S hS hsq) :=
  P

/-- A morphism `P ⟶ E|_V` of `D(𝒪_V)`, read in the spelling
`AlgebraicGeometry.Space.smallEtaleModulesDerived`. -/
abbrev edsSmallEtaleHom
    {P : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)}
    (αP : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) :
    edsSmallEtaleObj B S hS hsq P ⟶ edsEtaleRestrictSmallEtale B S hS hsq E :=
  αP

/-- Composition with `αP`, read in the two spellings of `D(𝒪_V)`. -/
theorem edsSmallEtaleHom_comp
    {P : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)}
    (αP : P ⟶ (edsEtaleRestrict B S hS hsq).obj E) {W : smallEtaleModulesDerived B S hS
      (edsEtale B S hS hsq)}
    (x : edsEtaleRestrictSmallEtale B S hS hsq E ⟶ W) :
    edsSmallEtaleHom B S hS hsq E αP ≫ x =
      (αP ≫ (x : (edsEtaleRestrict B S hS hsq).obj E ⟶ W) : P ⟶ W) :=
  rfl

/-- `AlgebraicGeometry.Space.edsSmallEtaleHom` is bijective on `Ext` groups into
`𝒢^•|_V ⊗ f|_V^*ℱ` when `αP` is. -/
theorem bijective_edsSmallEtaleHom_comp (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    {P : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2)}
    (αP : P ⟶ (edsEtaleRestrict B S hS hsq).obj E)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (i : ℤ)
    (hb : Function.Bijective (fun e : (edsEtaleRestrict B S hS hsq).obj E ⟶
      (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
        ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (ComplexShape.up ℤ) 0).obj F))⟦i⟧ => αP ≫ e)) :
    Function.Bijective (fun x : edsEtaleRestrictSmallEtale B S hS hsq E ⟶
      (extPerfectCoefficientObj B S hS (edsEtaleHom B S hS hsq ≫ f)
        ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G) F)⟦i⟧ => edsSmallEtaleHom B S
        hS hsq E αP ≫ x) :=
  hb

end Spelling


/-! ### Stacks 08JR (A) -/

/-- `𝒢^• ⊗ f^*ℱ` is supported in a set containing the supports of the `𝒢ⁿ`. -/
theorem cohomologySupportedOn_tensorPullbackComplexDerived_single (f : X ⟶ Y)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (T : Set (points B S hS X.1))
    (hG : ∀ n : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X n)) ⊆ T)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    CohomologySupportedOn B S hS X.1 X.2 T (tensorPullbackComplexDerived f G
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F)) :=
  cohomologySupportedOn_Q_obj_tensorPullbackComplex_single f G T hG F

/-- **Stacks 08JR, part (A).**  Let `S` be a scheme and `f : X ⟶ B` a morphism of algebraic spaces
over `S` with `B` Noetherian and `f` locally of finite type and quasi-separated.  Let
`E ∈ D^-_{Coh}(𝒪_X)` (coherent cohomology sheaves, bounded above) and let `𝒢^•` be a bounded
complex of coherent `𝒪_X`-modules, flat over `B`, with support proper over `B`.  Then for every
`m ∈ ℤ` there are a perfect `K ∈ D(𝒪_B)` and maps
`α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢^• ⊗_{𝒪_X} f^*ℱ) ⟶ H^i(B, K ⊗^L_{𝒪_B} ℱ)` for quasi-coherent
`𝒪_B`-modules `ℱ`, functorial in `ℱ`, compatible with the boundary maps of short exact sequences
`0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent modules (on the left the boundary map of the
distinguished triangle of `0 → 𝒢^• ⊗ f^*ℱ₁ → 𝒢^• ⊗ f^*ℱ₂ → 𝒢^• ⊗ f^*ℱ₃ → 0`, on the right the
connecting map of the cohomology of `RΓ(B, K ⊗^L -)` of the triangle of `ℱ₁[0] → ℱ₂[0] → ℱ₃[0]`),
and invertible for `i ≤ m`.

Here `Ext^i(E, -) = Hom(E, -[i])` in `D(𝒪_X)` (`AlgebraicGeometry.Space.tensorPullbackExtGroup`),
`H^i(B, K ⊗^L ℱ)` is the `i`-th cohomology of derived global sections of `K ⊗^L ℱ[0]`
(`AlgebraicGeometry.Space.smallEtaleTensorCohomology`), and the maps are morphisms of abelian
groups. -/
@[stacks 08JR "(A)"]
theorem exists_isPerfect_tensorPullbackExtGroup_smallEtaleTensorCohomology
    (hTop : B.Contains (⊤_ Scheme.{u}))
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1) (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hEcoh : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ q).obj E))
    (hEb : DerivedCategoryB.IsBoundedAbove E)
    (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)
    (hG : FlatProperSupportComplex B S hS f hf G) (m : ℤ) :
    ∃ (K : smallEtaleModulesDerived B S hS Y) (_ : SmallEtaleIsPerfect B S hS K)
      (α : ∀ (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (_ : F.IsQuasicoherentOnSite) (i : ℤ),
        tensorPullbackExtGroup B S hS E f G F i ⟶ smallEtaleTensorCohomology B S hS K F i),
      (∀ (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
        (hF : F.IsQuasicoherentOnSite) (i : ℤ), i ≤ m → IsIso (α F hF i)) ∧
      (∀ {F F' : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)}
        (hF : F.IsQuasicoherentOnSite) (hF' : F'.IsQuasicoherentOnSite) (q : F ⟶ F') (i : ℤ),
        tensorPullbackExtGroupMap B S hS E f G q i ≫ α F' hF' i =
          α F hF i ≫ smallEtaleTensorCohomologyMap B S hS K q i) ∧
      (∀ (T : ShortComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)))
        (hT : T.ShortExact) (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite)
        (i j : ℤ) (h : i + 1 = j),
        tensorPullbackExtGroupDelta B S hS E f G T (shortExact_tensorPullbackComplex_map_single
            (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT) i j h ≫
            α T.X₁ h₁ j =
          α T.X₃ h₃ i ≫ smallEtaleTensorCohomologyDelta B S hS K T hT i j h) := by
  obtain ⟨Z, hZ, V, hV, hsq, hZp, hGZ, hVqc, hcompl, hZV⟩ :=
    exists_isOpenSubspace_isElementaryDistinguishedSquare_of_flatProperSupportComplex B S hS hTop f
      hf hY G hG
  have hN := isNoetherian_edsEtale_openSubspaceOfPoints B S hS hTop f hf hfqs hY hsq hVqc
  have hGV := flatProperSupport_edsRestrictComplex B S hS hTop f hf hfqs hY G hG hsq hVqc hGZ
    hcompl (fun _ => hZp)
  obtain ⟨a, b, hab⟩ := hGV.bounded
  have hEV := isPseudoCoherent_edsEtaleRestrict_of_isCoherent_homology B S hS hsq hTop hN E hEcoh
    hEb
  obtain ⟨P, hP, αP, hαP⟩ := exists_isPerfect_bijective_comp_shiftedHom hTop
    (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2 hN.1 hN.2.1 _ hEV m a
  have hP' : SmallEtaleIsPerfect B S hS (edsSmallEtaleObj B S hS hsq P) := hP
  have hfV := isLocallyOfFiniteType_edsEtaleHom_comp B S hS hsq f hf
  have hfVqs := isQuasiSeparated_edsEtaleHom_comp B S hS hsq f hfqs
  obtain ⟨c, hcnat, hcδ⟩ := exists_extPerfectCohomologyIso B S hS hTop (edsEtaleHom B S hS hsq ≫ f)
    hfV hfVqs hY (edsSmallEtaleObj B S hS hsq P) hP' ((pullbackComplexSmallEtale
      (edsEtaleHom B S hS hsq)).obj G) hGV
  have hNF := cohomologySupportedOn_tensorPullbackComplexDerived_single B S hS f G _
    (fun q => (hGZ q).trans hcompl.symm.le)
  have hflat := FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hGV
  refine ⟨extPerfectDirectImageObj B S hS (edsEtaleHom B S hS hsq ≫ f)
      (edsSmallEtaleObj B S hS hsq P) ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G),
    isPerfect_extPerfectDirectImageObj B S hS hTop _ hfV hfVqs hY _ hP' _ hGV,
    fun F hF i => AddCommGrpCat.ofHom (AddMonoidHom.mk'
        (fun e => edsSmallEtaleHom B S hS hsq E αP ≫ edsRestrictSmallEtaleCast B S hS hsq f G E F i
          (edsRestrictCoefficientExtHom hsq f G E ((HomologicalComplex.single
            (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (ComplexShape.up ℤ) 0).obj
            F) i e))
        (edsApproxExt_add B S hS hsq f G E (edsSmallEtaleHom B S hS hsq E αP) F i)) ≫
      (c F hF i).inv, ?_, ?_, ?_⟩
  · intro F hF i hi
    have : (tensorPullbackComplexDerived (edsEtaleHom B S hS hsq ≫ f)
      ((pullbackComplexSmallEtale (edsEtaleHom B S hS hsq)).obj G)
      ((HomologicalComplex.single (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y))
      (ComplexShape.up ℤ) 0).obj F)).IsGE a :=
      isGE_Q_obj_tensorPullbackComplex_single _ _ a (fun n hn => hab n (Or.inl hn)) F
    have h1 := AddCommGrpCat.isIso_ofHom_mk'_of_bijective _
      (edsApproxExt_add B S hS hsq f G E (edsSmallEtaleHom B S hS hsq E αP) F i)
      (bijective_edsApproxExt B S hS hsq f G E (edsSmallEtaleHom B S hS hsq E αP) F (hNF F) i
        (bijective_edsSmallEtaleHom_comp B S hS hsq E f G αP F i (hαP _ i hi)))
    exact IsIso.comp_isIso' h1 (Iso.isIso_inv (c F hF i))
  · intro F F' hF hF' q i
    exact CategoryTheory.preadditiveCoyoneda_map_comp_ofHom_mk'_comp_inv _ _ _ _ _ _ _ _ _
      (edsApproxExt_naturality B S hS hsq f G E (edsSmallEtaleHom B S hS hsq E αP) q i)
      (hcnat F F' hF hF' q i)
  · intro T hT h₁ h₃ i j h
    subst h
    exact CategoryTheory.preadditiveCoyoneda_map_comp_ofHom_mk'_comp_inv _ _ _ _ _ _ _ _ _
      (edsApproxExt_delta_shift B S hS hsq f G E (edsSmallEtaleHom B S hS hsq E αP) T
        (shortExact_tensorPullbackComplex_map_single
          (FlatProperSupportComplex.isFlatOverAtGeometricPoint B S hS hG) hT)
        (shortExact_tensorPullbackComplex_map_single hflat hT) i)
      (hcδ T hT h₁ h₃ i (i + 1) rfl)

end AlgebraicGeometry.Space

end
