module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusExactSquare
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import
  StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMapFunctoriality

/-!
# Transporting a derived base change comparison along exact functors

Consider two squares of additive functors between abelian categories

```
T --F--> S            T' --F₁--> S'
|G'      |G           |G₁'       |G₁
v        v            v          v
Y --F'-> X            Y' --F₁'-> X'
```

with comparisons `τ : F ⋙ G ⟶ G' ⋙ F'` and `τ₁ : F₁ ⋙ G₁ ⟶ G₁' ⋙ F₁'`, the vertical functors `G`
and `G₁` exact, and exact functors `U_T`, `U_S`, `U_X`, `U_Y` from the corners of the first square
to those of the second, commuting with the four edges through isomorphisms `aF`, `aF'`, `aG`,
`aG'`, and carrying `τ` to `τ₁` (`hτ`). The comparisons descend to bounded below derived categories
(`Stacks.Cohomology.BaseChange.derived`), and if the `U`'s carry injectives to acyclics for the
edges of the second square, so that the edges' right derived functors commute with the `U`'s
(`CategoryTheory.Functor.rightDerivedFunctorPlusExactSquareIso`), then **the two descended
comparisons correspond under the `U`'s** (`derived_exactTransport_app`).

## Main results

* `Stacks.Cohomology.BaseChange.derived_exactTransport`: the descended comparisons correspond under
  the `U`'s, as transformations of functors `D⁺(T) ⥤ D⁺(X')`.
* `Stacks.Cohomology.BaseChange.derived_exactTransport_app`: the same identity at an object of
  `D⁺(T)`.
* `Stacks.Cohomology.BaseChange.mate_exactTransport_app`: the mate of a square of adjunctions
  transports along functors commuting with the four adjoints.

## Implementation notes

`Stacks.Cohomology.BaseChange.derived` is built under the standard model of the derived category,
which therefore fixes the model here.

Both sides are transformations out of `(RF ⋙ RG) ⋙ U_X`, which is a right derived functor of
degreewise `F` followed by `RG ⋙ U_X`; so they agree as soon as they agree after the unit, at the
image of every bounded below complex `K`. There each side is computed by the factorizations of the
descended comparisons (`Stacks.Cohomology.BaseChange.derived_fac_app`) and of the four commutation
isomorphisms (`rightDerivedFunctorPlusExactSquareIso_hom_app_Qh`), and what remains is `hτ` applied
degreewise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

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
  (aF : F ⋙ US ≅ UT ⋙ F₁) (aF' : F' ⋙ UX ≅ UY ⋙ F₁')
  (aG : G ⋙ UX ≅ US ⋙ G₁) (aG' : G' ⋙ UY ≅ UT ⋙ G₁')
  (hF : ∀ I : T, Injective I → F₁.rightAcyclic (UT.obj I))
  (hF' : ∀ I : Y, Injective I → F₁'.rightAcyclic (UY.obj I))
  (hG : ∀ I : S, Injective I → G₁.rightAcyclic (US.obj I))
  (hG' : ∀ I : T, Injective I → G₁'.rightAcyclic (UT.obj I))
  (τ : F ⋙ G ⟶ G' ⋙ F') (τ₁ : F₁ ⋙ G₁ ⟶ G₁' ⋙ F₁')

/-- For exact `G`, the unit of `G.rightDerivedFunctorPlus` is an isomorphism. -/
instance isIso_rightDerivedFunctorPlusUnit_exactG : IsIso G.rightDerivedFunctorPlusUnith :=
  exactUnit_isIso G
/-- For exact `G₁`, the unit of `G₁.rightDerivedFunctorPlus` is an isomorphism. -/
instance isIso_rightDerivedFunctorPlusUnit_exactG₁ : IsIso G₁.rightDerivedFunctorPlusUnith :=
  exactUnit_isIso G₁

/-- The unit exhibiting `(RF ⋙ RG) ⋙ U_X` as a right derived functor. -/
def exactTransportUnit :
    ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ G.rightDerivedFunctorPlus) ⋙
        UX.mapDerivedCategoryPlus ⟶
      DerivedCategory.Plus.Qh ⋙
        ((F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙ UX.mapDerivedCategoryPlus) :=
  Functor.whiskerRight (compUnit F G) UX.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom

/-- `(RF ⋙ RG) ⋙ U_X` is a right derived functor of `((F ⋙ Qh) ⋙ RG) ⋙ U_X` with respect to the
quasi-isomorphisms of `K⁺(T)`, with unit `exactTransportUnit`. -/
instance isRightDerivedFunctor_exactTransportUnit :
    ((F.rightDerivedFunctorPlus ⋙ G.rightDerivedFunctorPlus) ⋙
      UX.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (exactTransportUnit (F := F) (G := G) (UX := UX)) (HomotopyCategory.Plus.quasiIso T) :=
  LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso
    (HomotopyCategory.Plus.localizerMorphism_derives _) _
    (fun K ↦ by dsimp [exactTransportUnit, compUnit]; infer_instance)


omit [EnoughInjectives T] [EnoughInjectives S] [EnoughInjectives Y] [EnoughInjectives T']
  [EnoughInjectives S'] [EnoughInjectives Y'] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits UT] [PreservesFiniteColimits UT]
  [PreservesFiniteLimits US] [PreservesFiniteColimits US] [PreservesFiniteLimits UX]
  [PreservesFiniteColimits UX] [PreservesFiniteLimits UY] [PreservesFiniteColimits UY] in
variable {aF aF' aG aG' τ τ₁} in
/-- The transport hypothesis on `τ`, applied degreewise to a complex. -/
theorem mapHomologicalComplex_exactTransport
    (hτ : ∀ t : T, UX.map (τ.app t) ≫ aF'.hom.app (G'.obj t) ≫ F₁'.map (aG'.hom.app t) =
      aG.hom.app (F.obj t) ≫ G₁.map (aF.hom.app t) ≫ τ₁.app (UT.obj t))
    (L : CochainComplex T ℤ) :
    (UX.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app L) ≫
      (NatTrans.mapHomologicalComplex aF'.hom (ComplexShape.up ℤ)).app
        ((G'.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
      (F₁'.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex aG'.hom (ComplexShape.up ℤ)).app L) =
    (NatTrans.mapHomologicalComplex aG.hom (ComplexShape.up ℤ)).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
      (G₁.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex aF.hom (ComplexShape.up ℤ)).app L) ≫
      (NatTrans.mapHomologicalComplex τ₁ (ComplexShape.up ℤ)).app
        ((UT.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  ext i
  simpa using hτ (L.X i)

omit [EnoughInjectives T] [EnoughInjectives S] [EnoughInjectives Y] [EnoughInjectives T']
  [EnoughInjectives S'] [EnoughInjectives Y'] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [PreservesFiniteLimits UT] [PreservesFiniteColimits UT]
  [PreservesFiniteLimits US] [PreservesFiniteColimits US] [PreservesFiniteLimits UX]
  [PreservesFiniteColimits UX] [PreservesFiniteLimits UY] [PreservesFiniteColimits UY] in
variable {aF aF' aG aG' τ τ₁} in
/-- **The degreewise transport of the comparison**, on the bounded below homotopy category. -/
theorem mapPlus_exactTransport
    (hτ : ∀ t : T, UX.map (τ.app t) ≫ aF'.hom.app (G'.obj t) ≫ F₁'.map (aG'.hom.app t) =
      aG.hom.app (F.obj t) ≫ G₁.map (aF.hom.app t) ≫ τ₁.app (UT.obj t))
    (K : HomotopyCategory.Plus T) :
    UX.mapHomotopyCategoryPlus.map ((mapPlus τ).app K) ≫
        (mapPlus aF'.hom).app (G'.mapHomotopyCategoryPlus.obj K) ≫
        F₁'.mapHomotopyCategoryPlus.map ((mapPlus aG'.hom).app K) =
      (mapPlus aG.hom).app (F.mapHomotopyCategoryPlus.obj K) ≫
        G₁.mapHomotopyCategoryPlus.map ((mapPlus aF.hom).app K) ≫
        (mapPlus τ₁).app (UT.mapHomotopyCategoryPlus.obj K) := by
  obtain ⟨⟨L⟩, hL⟩ := K
  ext
  refine Eq.trans ?_ ((congrArg (fun z => (HomotopyCategory.quotient X' (ComplexShape.up ℤ)).map z)
    (mapHomologicalComplex_exactTransport hτ L)).trans ?_) <;>
  (rw [Functor.map_comp, Functor.map_comp]; rfl)

section Chase

variable {𝒞 : Type*} [Category* 𝒞]

/-- In an arbitrary category, given the commutation identities `h1`–`h6`, `r1`–`r6`, `hc`, `hv`,
`hx1`, `hx2` and `hZ` between the named morphisms, the composites `U₀ ≫ D₀ ≫ I₁ ≫ J₁` and
`U₀ ≫ G₀ ≫ Fm ≫ D₁` are equal. -/
theorem exactTransport_chase
    {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ Z₁ W₀ W₁ W₂ W₃ V₁ V₂ V₃ R₁ R₂ T₁ T₃ T₄ P₁ Q₁ Q₂ : 𝒞}
    (U₀ : X₀ ⟶ X₁) (D₀ : X₁ ⟶ X₂) (I₁ : X₂ ⟶ X₃) (J₁ : X₃ ⟶ X₄)
    (A₁ : X₀ ⟶ Y₁) (A₂ : Y₁ ⟶ Y₂) (A₃ : Y₂ ⟶ Y₃) (A₄ : Y₃ ⟶ X₂)
    (h1 : U₀ ≫ D₀ = A₁ ≫ A₂ ≫ A₃ ≫ A₄)
    (I₂ : Y₃ ⟶ Z₁) (B : Z₁ ⟶ X₃) (h2 : A₄ ≫ I₁ = I₂ ≫ B)
    (S₁ : Y₂ ⟶ W₁) (S₂ : W₁ ⟶ W₂) (S₃ : W₂ ⟶ W₃) (S₄ : W₃ ⟶ Z₁)
    (h3 : A₃ ≫ I₂ = S₁ ≫ S₂ ≫ S₃ ≫ S₄)
    (C₁ : Z₁ ⟶ W₃) (C₂ : W₃ ⟶ V₂) (C₃ : V₂ ⟶ V₃) (C₅ : V₃ ⟶ X₄)
    (h4 : B ≫ J₁ = C₁ ≫ C₂ ≫ C₃ ≫ C₅) (hc : S₄ ≫ C₁ = 𝟙 W₃)
    (S₁' : Y₁ ⟶ W₀) (M₁ : W₀ ⟶ W₁) (h5 : A₂ ≫ S₁ = S₁' ≫ M₁)
    (M₃ : W₂ ⟶ V₁) (S₃' : V₁ ⟶ V₂) (h6 : S₃ ≫ C₂ = M₃ ≫ S₃')
    (G₀ : X₁ ⟶ R₁) (Fm : R₁ ⟶ R₂) (D₁ : R₂ ⟶ X₄)
    (G₀' : X₀ ⟶ T₁) (W₀' : T₁ ⟶ R₁) (r1 : U₀ ≫ G₀ = G₀' ≫ W₀')
    (W₁' : T₁ ⟶ Q₂) (W₂' : Q₂ ⟶ T₃) (W₃' : T₃ ⟶ T₄) (W₄' : T₄ ⟶ R₂)
    (r2 : W₀' ≫ Fm = W₁' ≫ W₂' ≫ W₃' ≫ W₄')
    (D₁' : T₄ ⟶ V₃) (r3 : W₄' ≫ D₁ = D₁' ≫ C₅)
    (O₁ : T₃ ⟶ P₁) (O₂ : P₁ ⟶ V₁) (r4 : W₃' ≫ D₁' = O₁ ≫ O₂ ≫ S₃' ≫ C₃)
    (O₁' : Q₂ ⟶ Q₁) (N₂ : Q₁ ⟶ P₁) (r5 : W₂' ≫ O₁ = O₁' ≫ N₂)
    (V : Y₁ ⟶ X₀) (hv : A₁ ≫ V = 𝟙 X₀)
    (N₁ : W₀ ⟶ Q₁) (X₁' : Q₁ ⟶ Q₂) (X₂' : Q₂ ⟶ T₁)
    (r6 : V ≫ G₀' = S₁' ≫ N₁ ≫ X₁' ≫ X₂')
    (hx2 : X₂' ≫ W₁' = 𝟙 Q₂) (hx1 : X₁' ≫ O₁' = 𝟙 Q₁)
    (hZ : M₁ ≫ S₂ ≫ M₃ = N₁ ≫ N₂ ≫ O₂) :
    U₀ ≫ D₀ ≫ I₁ ≫ J₁ = U₀ ≫ G₀ ≫ Fm ≫ D₁ := by
  have hL : U₀ ≫ D₀ ≫ I₁ ≫ J₁ = A₁ ≫ S₁' ≫ M₁ ≫ S₂ ≫ M₃ ≫ S₃' ≫ C₃ ≫ C₅ := by
    rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, h4, reassoc_of% hc, reassoc_of% h5,
      reassoc_of% h6]
  have hG : G₀' = A₁ ≫ S₁' ≫ N₁ ≫ X₁' ≫ X₂' := by
    rw [← r6, ← Category.assoc, hv, Category.id_comp]
  have hR : U₀ ≫ G₀ ≫ Fm ≫ D₁ = A₁ ≫ S₁' ≫ N₁ ≫ N₂ ≫ O₂ ≫ S₃' ≫ C₃ ≫ C₅ := by
    rw [reassoc_of% r1, reassoc_of% r2, r3, reassoc_of% r4, reassoc_of% r5, hG]
    simp only [Category.assoc]
    rw [reassoc_of% hx2, reassoc_of% hx1]
  rw [hL, hR, reassoc_of% hZ]

variable {𝒦 𝒦₁ 𝒦₂ : Type*} [Category* 𝒦] [Category* 𝒦₁] [Category* 𝒦₂]

/-- The degreewise transport, read through a functor and with identity morphisms inserted. -/
theorem exactTransport_chaseZ (Q : 𝒦 ⥤ 𝒞) (P₁ : 𝒦₁ ⥤ 𝒦) (P₂ : 𝒦₂ ⥤ 𝒦)
    {a b c₂ c₄ : 𝒦} {b₁ c₁ c₃ : 𝒦₁} {a₂ b₂ c₅ : 𝒦₂}
    (x₀ : a ⟶ b) (k₂ : b ⟶ c₂) (r₂ : c₂ ⟶ P₁.obj b₁) (k₂' : b ⟶ P₁.obj b₁)
    (k₃ : b₁ ⟶ c₃) (r₃ : c₃ ⟶ c₁) (k₃' : b₁ ⟶ c₁)
    (k₄ : a ⟶ c₄) (r₄ : c₄ ⟶ P₂.obj a₂) (k₄' : a ⟶ P₂.obj a₂)
    (k₅ : a₂ ⟶ c₅) (r₅ : c₅ ⟶ b₂) (k₅' : a₂ ⟶ b₂) (k₆ : P₂.obj b₂ ⟶ P₁.obj c₁)
    (h : x₀ ≫ k₂' ≫ P₁.map k₃' = k₄' ≫ P₂.map k₅' ≫ k₆)
    (hk₂ : k₂ ≫ r₂ = k₂') (hk₃ : k₃ ≫ r₃ = k₃') (hk₄ : k₄ ≫ r₄ = k₄') (hk₅ : k₅ ≫ r₅ = k₅') :
    Q.map x₀ ≫ Q.map (k₂ ≫ r₂) ≫ Q.map (P₁.map (k₃ ≫ r₃)) =
      Q.map (k₄ ≫ r₄) ≫ Q.map (P₂.map (k₅ ≫ r₅)) ≫ Q.map k₆ := by
  rw [hk₂, hk₃, hk₄, hk₅, ← Q.map_comp, ← Q.map_comp, h, Q.map_comp, Q.map_comp]

/-- A functor applied to a composite of four morphisms. -/
theorem map_comp₄ {𝒟 : Type*} [Category* 𝒟] (Φ : 𝒟 ⥤ 𝒞) {a b c d e : 𝒟} (f₁ : a ⟶ b)
    (f₂ : b ⟶ c) (f₃ : c ⟶ d) (f₄ : d ⟶ e) :
    Φ.map (f₁ ≫ f₂ ≫ f₃ ≫ f₄) = Φ.map f₁ ≫ Φ.map f₂ ≫ Φ.map f₃ ≫ Φ.map f₄ := by
  simp

/-- A functor carries a composite equal to a composite of four morphisms to such an equation. -/
private theorem map_comp_eq_map_comp₄ {𝒟 : Type*} [Category* 𝒟] (Φ : 𝒟 ⥤ 𝒞) {a b c d e f : 𝒟}
    {u : a ⟶ b} {v : b ⟶ c} {f₁ : a ⟶ d} {f₂ : d ⟶ e} {f₃ : e ⟶ f} {f₄ : f ⟶ c}
    (h : u ≫ v = f₁ ≫ f₂ ≫ f₃ ≫ f₄) :
    Φ.map u ≫ Φ.map v = Φ.map f₁ ≫ Φ.map f₂ ≫ Φ.map f₃ ≫ Φ.map f₄ := by
  rw [← Φ.map_comp, h, map_comp₄]

/-- A functor carries a composite equal to the identity to such an equation. -/
private theorem map_comp_eq_id {𝒟 : Type*} [Category* 𝒟] (Φ : 𝒟 ⥤ 𝒞) {a b : 𝒟}
    {u : a ⟶ b} {v : b ⟶ a} (h : u ≫ v = 𝟙 a) : Φ.map u ≫ Φ.map v = 𝟙 _ := by
  rw [← Φ.map_comp, h, Φ.map_id]

end Chase

variable {aF aF' aG aG' τ τ₁} in
/-- **The transport at the image of a bounded below complex, after the unit.** -/
theorem derived_exactTransport_aux
    (hτ : ∀ t : T, UX.map (τ.app t) ≫ aF'.hom.app (G'.obj t) ≫ F₁'.map (aG'.hom.app t) =
      aG.hom.app (F.obj t) ≫ G₁.map (aF.hom.app t) ≫ τ₁.app (UT.obj t))
    (K : HomotopyCategory.Plus T) :
    UX.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlus.map
        (F.rightDerivedFunctorPlusUnith.app K)) ≫
      UX.mapDerivedCategoryPlus.map ((derived F F' G G' τ
        (asIso G.rightDerivedFunctorPlusUnith)).app (DerivedCategory.Plus.Qh.obj K)) ≫
      (Functor.rightDerivedFunctorPlusExactSquareIso aF' hF').hom.app
        (G'.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      F₁'.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusExactSquareIso aG' hG').hom.app
          (DerivedCategory.Plus.Qh.obj K)) =
    UX.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlus.map
        (F.rightDerivedFunctorPlusUnith.app K)) ≫
      (Functor.rightDerivedFunctorPlusExactSquareIso aG hG).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Qh.obj K)) ≫
      G₁.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusExactSquareIso aF hF).hom.app
          (DerivedCategory.Plus.Qh.obj K)) ≫
      (derived F₁ F₁' G₁ G₁' τ₁ (asIso G₁.rightDerivedFunctorPlusUnith)).app
        (UT.mapDerivedCategoryPlus.obj (DerivedCategory.Plus.Qh.obj K)) := by
  have l1 := derived_fac_app F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith) K
  rw [onHomotopy_app] at l1
  have l2 := (Functor.rightDerivedFunctorPlusExactSquareIso aF' hF').hom.naturality
    (G'.rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.comp_map] at l2
  have l4 := Functor.rightDerivedFunctorPlusExactSquareIso_hom_app_Qh aG' hG' K
  have l5 := UX.mapDerivedCategoryPlusFactorsh.hom.naturality ((mapPlus τ).app K)
  simp only [Functor.comp_map] at l5
  have l6 := (F₁'.rightDerivedFunctorPlusUnith.naturality
    ((Functor.mapHomotopyCategoryPlusCompIso aG').hom.app K ≫
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (UT ⋙ G₁'))).inv.app K)).symm
  simp only [Functor.comp_map] at l6
  have r1 := (Functor.rightDerivedFunctorPlusExactSquareIso aG hG).hom.naturality
    (F.rightDerivedFunctorPlusUnith.app K)
  simp only [Functor.comp_map] at r1
  have r2 := Functor.rightDerivedFunctorPlusExactSquareIso_hom_app_Qh aF hF K
  have r3 := (derived F₁ F₁' G₁ G₁' τ₁ (asIso G₁.rightDerivedFunctorPlusUnith)).naturality
    (UT.mapDerivedCategoryPlusFactorsh.inv.app K)
  simp only [Functor.comp_map] at r3
  have r4 := derived_fac_app F₁ F₁' G₁ G₁' τ₁ (asIso G₁.rightDerivedFunctorPlusUnith)
    (UT.mapHomotopyCategoryPlus.obj K)
  rw [onHomotopy_app] at r4
  have r5 := (asIso G₁.rightDerivedFunctorPlusUnith).inv.naturality
    ((Functor.mapHomotopyCategoryPlusCompIso aF).hom.app K ≫
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (UT ⋙ F₁))).inv.app K)
  simp only [Functor.comp_map] at r5
  have r6 := Functor.rightDerivedFunctorPlusExactSquareIso_hom_app_Qh aG hG
    (F.mapHomotopyCategoryPlus.obj K)
  have h1 := map_comp_eq_map_comp₄ UX.mapDerivedCategoryPlus l1
  have h3 := Functor.rightDerivedFunctorPlusExactSquareIso_hom_app_Qh aF' hF'
    (G'.mapHomotopyCategoryPlus.obj K)
  have h4 := map_comp_eq_map_comp₄ F₁'.rightDerivedFunctorPlus l4
  have hc := map_comp_eq_id F₁'.rightDerivedFunctorPlus
    (UY.mapDerivedCategoryPlusFactorsh.inv_hom_id_app (G'.mapHomotopyCategoryPlus.obj K))
  have hr2 := map_comp_eq_map_comp₄ G₁.rightDerivedFunctorPlus r2
  have hv := map_comp_eq_id UX.mapDerivedCategoryPlus
    ((asIso G.rightDerivedFunctorPlusUnith).inv_hom_id_app (F.mapHomotopyCategoryPlus.obj K))
  have hx2 := map_comp_eq_id G₁.rightDerivedFunctorPlus
    (US.mapDerivedCategoryPlusFactorsh.inv_hom_id_app (F.mapHomotopyCategoryPlus.obj K))
  have hx1 := (asIso G₁.rightDerivedFunctorPlusUnith).hom_inv_id_app
    (US.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K))
  have hZ := exactTransport_chaseZ DerivedCategory.Plus.Qh F₁'.mapHomotopyCategoryPlus
    G₁.mapHomotopyCategoryPlus (b₁ := UY.mapHomotopyCategoryPlus.obj
      (G'.mapHomotopyCategoryPlus.obj K))
    (c₁ := G₁'.mapHomotopyCategoryPlus.obj (UT.mapHomotopyCategoryPlus.obj K))
    (a₂ := US.mapHomotopyCategoryPlus.obj (F.mapHomotopyCategoryPlus.obj K))
    (b₂ := F₁.mapHomotopyCategoryPlus.obj (UT.mapHomotopyCategoryPlus.obj K))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mapPlus_exactTransport hτ K)
    (mapHomotopyCategoryPlusCompIso_refl_comp_inv _)
    (mapHomotopyCategoryPlusCompIso_refl_comp_inv _)
    (mapHomotopyCategoryPlusCompIso_refl_comp_inv _)
    (mapHomotopyCategoryPlusCompIso_refl_comp_inv _)
  exact exactTransport_chase _ _ _ _ _ _ _ _ h1 _ _ l2 _ _ _ _ h3 _ _ _ _ h4 hc _ _ l5 _ _ l6
    _ _ _ _ _ r1 _ _ _ _ hr2 _ r3 _ _ r4 _ _ r5 _ hv _ _ _ r6 hx2 hx1 hZ

variable {aF aF' aG aG' τ τ₁} in
/-- **The descended comparisons correspond under the exact functors**, as transformations of
functors `D⁺(T) ⥤ D⁺(X')`: `R(τ)` carried by `U_X` and read through the commutation isomorphisms
of `RF'` and `RG'` with the `U`'s is `R(τ₁)` at the `U_T`-images, read through those of `RF`
and `RG`. -/
theorem derived_exactTransport
    (hτ : ∀ t : T, UX.map (τ.app t) ≫ aF'.hom.app (G'.obj t) ≫ F₁'.map (aG'.hom.app t) =
      aG.hom.app (F.obj t) ≫ G₁.map (aF.hom.app t) ≫ τ₁.app (UT.obj t)) :
    Functor.whiskerRight (derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith))
        UX.mapDerivedCategoryPlus ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft G'.rightDerivedFunctorPlus
        (Functor.rightDerivedFunctorPlusExactSquareIso aF' hF').hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusExactSquareIso aG' hG').hom
        F₁'.rightDerivedFunctorPlus ≫ (Functor.associator _ _ _).hom =
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft F.rightDerivedFunctorPlus
        (Functor.rightDerivedFunctorPlusExactSquareIso aG hG).hom ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusExactSquareIso aF hF).hom
        G₁.rightDerivedFunctorPlus ≫ (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft UT.mapDerivedCategoryPlus
        (derived F₁ F₁' G₁ G₁' τ₁ (asIso G₁.rightDerivedFunctorPlusUnith)) := by
  refine Functor.rightDerived_ext _ (exactTransportUnit (F := F) (G := G) (UX := UX))
    (HomotopyCategory.Plus.quasiIso T) _ _ _ ?_
  refine NatTrans.ext (funext fun K => ?_)
  simp only [exactTransportUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, compUnit_app, Functor.comp_obj, Category.assoc]
  exact derived_exactTransport_aux hF hF' hG hG' hτ K

variable {aF aF' aG aG' τ τ₁} in
/-- **`derived_exactTransport` at an object** `M` of `D⁺(T)`:
`U_X(R(τ)_M)`, followed by the commutation isomorphisms of `RF'` and `RG'` with the `U`'s, is the
commutation isomorphisms of `RG` and `RF` followed by `R(τ₁)` at `U_T(M)`. -/
theorem derived_exactTransport_app
    (hτ : ∀ t : T, UX.map (τ.app t) ≫ aF'.hom.app (G'.obj t) ≫ F₁'.map (aG'.hom.app t) =
      aG.hom.app (F.obj t) ≫ G₁.map (aF.hom.app t) ≫ τ₁.app (UT.obj t))
    (M : DerivedCategory.Plus T) :
    UX.mapDerivedCategoryPlus.map
        ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app M) ≫
      (Functor.rightDerivedFunctorPlusExactSquareIso aF' hF').hom.app
        (G'.rightDerivedFunctorPlus.obj M) ≫
      F₁'.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusExactSquareIso aG' hG').hom.app M) =
    (Functor.rightDerivedFunctorPlusExactSquareIso aG hG).hom.app
        (F.rightDerivedFunctorPlus.obj M) ≫
      G₁.rightDerivedFunctorPlus.map
        ((Functor.rightDerivedFunctorPlusExactSquareIso aF hF).hom.app M) ≫
      (derived F₁ F₁' G₁ G₁' τ₁ (asIso G₁.rightDerivedFunctorPlusUnith)).app
        (UT.mapDerivedCategoryPlus.obj M) := by
  simpa using NatTrans.congr_app (derived_exactTransport hF hF' hG hG' hτ) M

/-! ### The underived comparison, transported -/

section UnderivedTransport

variable {𝒯 𝒮 𝒳 𝒴 𝒯' 𝒮' 𝒳' 𝒴' : Type*} [Category* 𝒯] [Category* 𝒮] [Category* 𝒳]
  [Category* 𝒴] [Category* 𝒯'] [Category* 𝒮'] [Category* 𝒳'] [Category* 𝒴']
  {Lf : 𝒮 ⥤ 𝒳} {Pf : 𝒳 ⥤ 𝒮} (adjf : Lf ⊣ Pf) {Le : 𝒯 ⥤ 𝒴} {Pe : 𝒴 ⥤ 𝒯} (adje : Le ⊣ Pe)
  {Lf₁ : 𝒮' ⥤ 𝒳'} {Pf₁ : 𝒳' ⥤ 𝒮'} (adjf₁ : Lf₁ ⊣ Pf₁)
  {Le₁ : 𝒯' ⥤ 𝒴'} {Pe₁ : 𝒴' ⥤ 𝒯'} (adje₁ : Le₁ ⊣ Pe₁)
  {Pg : 𝒯 ⥤ 𝒮} {Ph : 𝒴 ⥤ 𝒳} {Pg₁ : 𝒯' ⥤ 𝒮'} {Ph₁ : 𝒴' ⥤ 𝒳'}
  {σ : Pe ⋙ Pg ≅ Ph ⋙ Pf} {σ₁ : Pe₁ ⋙ Pg₁ ≅ Ph₁ ⋙ Pf₁}
  {UT : 𝒯 ⥤ 𝒯'} {US : 𝒮 ⥤ 𝒮'} {UX : 𝒳 ⥤ 𝒳'} {UY : 𝒴 ⥤ 𝒴'}
  {ρg : Pg ⋙ US ≅ UT ⋙ Pg₁} {ρh : Ph ⋙ UX ≅ UY ⋙ Ph₁} {ρf : Pf ⋙ US ≅ UX ⋙ Pf₁}
  {ρe : Pe ⋙ UT ≅ UY ⋙ Pe₁} {lf : Lf ⋙ UX ≅ US ⋙ Lf₁} {le : Le ⋙ UY ≅ UT ⋙ Le₁}

/-- The components of a mate, unfolded. -/
private theorem mate_app_eq {A B C D : Type*} [Category* A] [Category* B] [Category* C]
    [Category* D] {L : B ⥤ C} {P : C ⥤ B} (adj : L ⊣ P) {L' : A ⥤ D} {P' : D ⥤ A}
    (adj' : L' ⊣ P') (F : A ⥤ B) (F' : D ⥤ C) (e : P' ⋙ F ≅ F' ⋙ P) (a : A) :
    (mate adj adj' F F' e).app a =
      L.map (F.map (adj'.unit.app a) ≫ e.hom.app (L'.obj a)) ≫
        adj.counit.app (F'.obj (L'.obj a)) := by
  simp [mate]

/-- **The mate of a square of adjunctions transports along functors commuting with the four
adjoints.** If `U_X` carries the counit of `L_f ⊣ P_f` to that of `L_{f,1} ⊣ P_{f,1}` and `U_T`
the unit of `L_e ⊣ P_e` to that of `L_{e,1} ⊣ P_{e,1}`, through the commutation isomorphisms of
the adjoints, and the comparisons `σ`, `σ₁` of the composite right adjoints correspond, then the
mates `Stacks.Cohomology.BaseChange.mate` of `σ` and `σ₁` correspond. -/
theorem mate_exactTransport_app
    (hcounit : ∀ x : 𝒳, UX.map (adjf.counit.app x) =
      lf.hom.app (Pf.obj x) ≫ Lf₁.map (ρf.hom.app x) ≫ adjf₁.counit.app (UX.obj x))
    (hunit : ∀ t : 𝒯, UT.map (adje.unit.app t) ≫ ρe.hom.app (Le.obj t) ≫
      Pe₁.map (le.hom.app t) = adje₁.unit.app (UT.obj t))
    (hσ : ∀ y : 𝒴, US.map (σ.hom.app y) ≫ ρf.hom.app (Ph.obj y) ≫ Pf₁.map (ρh.hom.app y) =
      ρg.hom.app (Pe.obj y) ≫ Pg₁.map (ρe.hom.app y) ≫ σ₁.hom.app (UY.obj y))
    (t : 𝒯) :
    UX.map ((mate adjf adje Pg Ph σ).app t) ≫ ρh.hom.app (Le.obj t) ≫
        Ph₁.map (le.hom.app t) =
      lf.hom.app (Pg.obj t) ≫ Lf₁.map (ρg.hom.app t) ≫
        (mate adjf₁ adje₁ Pg₁ Ph₁ σ₁).app (UT.obj t) := by
  rw [mate_app_eq adjf adje Pg Ph σ t, mate_app_eq adjf₁ adje₁ Pg₁ Ph₁ σ₁ (UT.obj t),
    Functor.map_comp, hcounit]
  have n1 := lf.hom.naturality (Pg.map (adje.unit.app t) ≫ σ.hom.app (Le.obj t))
  simp only [Functor.comp_map] at n1
  rw [reassoc_of% n1]
  have n2 := adjf₁.counit.naturality (ρh.hom.app (Le.obj t) ≫ Ph₁.map (le.hom.app t))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at n2
  simp only [Category.assoc]
  rw [← n2, ← hunit]
  have n3 := ρg.hom.naturality (adje.unit.app t)
  simp only [Functor.comp_map, Functor.comp_obj] at n3
  have n4 := σ₁.hom.naturality (le.hom.app t)
  simp only [Functor.comp_map, Functor.comp_obj] at n4
  have inner : US.map (Pg.map (adje.unit.app t) ≫ σ.hom.app (Le.obj t)) ≫
      ρf.hom.app (Ph.obj (Le.obj t)) ≫
        Pf₁.map (ρh.hom.app (Le.obj t) ≫ Ph₁.map (le.hom.app t)) =
      ρg.hom.app t ≫ Pg₁.map (UT.map (adje.unit.app t) ≫ ρe.hom.app (Le.obj t) ≫
        Pe₁.map (le.hom.app t)) ≫ σ₁.hom.app (Le₁.obj (UT.obj t)) := by
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, reassoc_of% (hσ (Le.obj t)),
      reassoc_of% n3]
    simp only [Functor.map_comp, Category.assoc]
    rw [← n4]
  have h' := congrArg (fun z => lf.hom.app (Pg.obj t) ≫ Lf₁.map z ≫
    adjf₁.counit.app (Ph₁.obj (Le₁.obj (UT.obj t)))) inner
  simpa only [Functor.map_comp, Category.assoc] using h'

end UnderivedTransport

end Stacks.Cohomology.BaseChange

end
