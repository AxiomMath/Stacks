module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBoundary
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.SheafTensorPairing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.IntegerCoefficients
import StacksCore.Tactic.StacksAttribute

/-!
# The cup product and the boundary maps, for maps of complexes `Tot(Fᵢ ⊗ Gᵢ) ⟶ H`

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` and `0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` be short exact sequences of bounded below
complexes of `𝒪_X`-modules, `H` a bounded below complex, and `γᵢ : Tot(Fᵢ ⊗_{𝒪_X} Gᵢ) ⟶ H` maps
of complexes making the two squares of [Stacks, Tag 07MC] commute.  If Čech cohomology agrees
with cohomology for the sheaves `Fᵢᵖ` and `Gⱼ^q`, then for `a₃ ∈ Hⁿ(X, F₃)` and `b₁ ∈ Hᵐ(X, G₁)`

`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)`  in `H^{n+m+1}(X, H)`.

A map of complexes `γ : Tot(F ⊗_{𝒪_X} G) ⟶ H` induces a pairing on sections
`F^a(Z) ⊗_{Γ(X, 𝒪_X)} G^b(Z) ⟶ H^{a+b}(Z)`: the base change to `𝒪_X(Z)`, the map to the
sections of the sheaf tensor product, the inclusion of the summand and `γ`.  The commutative
squares of maps of complexes give the compatibility of these pairings, and the identity is
`Stacks.Cech.Hypercohomology.cup_boundary_of_pairing` for them.

Every statement mentioning the total complex `Tot(F ⊗_{𝒪_X} G)` names the existing instance
`(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat` with `letI := inferInstance`
(which inlines it, so the elaborated statement is unchanged).  The total complex asks for
`∀ F, ((sheafTensor O).obj F).Additive`, a single synthesis goal inside whose binder the search
for that instance would be repeated for every candidate, exhausting the synthesis budget.

## Main definitions

* `Stacks.Cech.LinearCupProduct.ComplexPairing.comp`: a pairing followed by a map of complexes.
* `Stacks.Cech.Hypercohomology.tensorPairing`: the pairing induced by a map of complexes
  `Tot(F ⊗_{𝒪_X} G) ⟶ H`.

## Main results

* `Stacks.Cech.Hypercohomology.tensorPairing_square`: commutative squares of maps of complexes
  give the compatibility of the induced pairings.
* `Stacks.Cech.Hypercohomology.cup_boundary`: [Stacks, Tag 07MC].
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf sheafTensor)
open Stacks.Cohomology.CechSheaf (SectionRing)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)

universe u

namespace Stacks.Cech.LinearCupProduct

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

section Comp

variable {C : Type*} [Category* C] {R : Type u} [CommRing R]
  {K L M M' : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **A pairing of complexes followed by a morphism of complexes** is a pairing of complexes. -/
noncomputable def ComplexPairing.comp (D : ComplexPairing R K L M) (φ : M ⟶ M') :
    ComplexPairing R K L M' where
  μ a b n h := D.μ a b n h ≫ φ.f n
  μ_d a b n h := by
    rw [Category.assoc, φ.comm, ← Category.assoc, D.μ_d a b n h]
    simp only [Preadditive.add_comp, Units.smul_def, Preadditive.zsmul_comp, Category.assoc]

/-- The components of `D.comp φ` are those of `D` followed by the components of `φ`. -/
theorem ComplexPairing.comp_μ (D : ComplexPairing R K L M) (φ : M ⟶ M') (a b n : ℤ)
    (h : a + b = n) : (D.comp φ).μ a b n h = D.μ a b n h ≫ φ.f n :=
  rfl

end Comp

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-! ### The pairing induced by a map of complexes `Tot(F ⊗_{𝒪_X} G) ⟶ H` -/

section TensorPairing

variable {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}

/-- **The pairing induced by a map of complexes `γ : Tot(F ⊗_{𝒪_X} G) ⟶ H`**: on sections over an
open `Z`, `F^a(Z) ⊗_{Γ(X, 𝒪_X)} G^b(Z) ⟶ (F^a ⊗_{𝒪_X} G^b)(Z) ⟶ Tot(F ⊗ G)^{a+b}(Z) ⟶ H^{a+b}(Z)`,
the base change to `𝒪_X(Z)` followed by sheafification, the inclusion of the summand, and `γ`.
The Leibniz rule is that of the total differential, carried by `γ`. -/
noncomputable def tensorPairing
    (γ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor F.obj G.obj (sheafTensor O) (up ℤ) ⟶ H.obj) :
    Pairing O F G H :=
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  (Stacks.Cech.SheafTensorPairing.sheafTensorComplexPairing O ⊤ F.obj G.obj).comp
    ((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map γ)

/-- The component of `tensorPairing O γ` in bidegree `(a, b)` is `sheafTensorPairing` followed by
the sections of the inclusion of the summand `F^a ⊗_{𝒪_X} G^b` and of `γ.f n`. -/
theorem tensorPairing_μ
    (γ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor F.obj G.obj (sheafTensor O) (up ℤ) ⟶ H.obj) (a b n : ℤ)
    (h : a + b = n) :
    letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
    (tensorPairing O γ).μ a b n h =
      Stacks.Cech.SheafTensorPairing.sheafTensorPairing O ⊤ (F.obj.X a) (G.obj.X b) ≫
        (Stacks.Cech.ModuleCupProduct.sectionsFunctor O ⊤).map
          (HomologicalComplex.ιMapBifunctor F.obj G.obj (sheafTensor O) (up ℤ) a b n h ≫
            γ.f n) := by
  rw [Functor.map_comp, ← Category.assoc]
  rfl

end TensorPairing

/-- Two composites through a common factor, stated with every object and morphism a variable. -/
theorem comp_eq_comp_of_factor {C : Type*} [Category* C] {A B M₁ M₂ E : C} (x : A ⟶ M₁)
    (y : A ⟶ M₂) (p : A ⟶ B) (s₁ : B ⟶ M₁) (s₂ : B ⟶ M₂) (t₁ : M₁ ⟶ E) (t₂ : M₂ ⟶ E)
    (hx : x = p ≫ s₁) (hy : y = p ≫ s₂) (h : s₁ ≫ t₁ = s₂ ≫ t₂) : x ≫ t₁ = y ≫ t₂ := by
  rw [hx, hy, Category.assoc, Category.assoc, h]

/-- **The commutative squares of maps of complexes give the compatibility of the induced
pairings.**  If `γ₁ ∘ (1 ⊗ v) = γ₂ ∘ (u ⊗ 1)` as maps of complexes
`Tot(F₁ ⊗ G₂) ⟶ H`, then the induced pairings on sections satisfy the same identity. -/
theorem tensorPairing_square
    {F₁ F₂ G₁ G₂ H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (u : F₁ ⟶ F₂) (v : G₂ ⟶ G₁)
    (γ₁ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor F₁.obj G₁.obj (sheafTensor O) (up ℤ) ⟶ H.obj)
    (γ₂ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor F₂.obj G₂.obj (sheafTensor O) (up ℤ) ⟶ H.obj)
    (h : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctorMap (𝟙 F₁.obj) v.hom (sheafTensor O) (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap u.hom (𝟙 G₂.obj) (sheafTensor O) (up ℤ) ≫ γ₂)
    (a b n : ℤ) (hn : a + b = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
        (((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).obj F₁.obj).X a)).map
        (((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map v.hom).f b) ≫
        (tensorPairing O γ₁).μ a b n hn =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
        (((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).map u.hom).f a)).app
          (((Stacks.Cech.ModuleCupProduct.sectionsComplexFunctor O ⊤).obj G₂.obj).X b) ≫
        (tensorPairing O γ₂).μ a b n hn := by
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance
  have key : ((sheafTensor O).obj (F₁.obj.X a)).map (v.hom.f b) ≫
      HomologicalComplex.ιMapBifunctor F₁.obj G₁.obj (sheafTensor O) (up ℤ) a b n hn ≫ γ₁.f n =
      ((sheafTensor O).map (u.hom.f a)).app (G₂.obj.X b) ≫
        HomologicalComplex.ιMapBifunctor F₂.obj G₂.obj (sheafTensor O) (up ℤ) a b n hn ≫
          γ₂.f n := by
    have := congrArg (fun φ => HomologicalComplex.ιMapBifunctor F₁.obj G₂.obj (sheafTensor O)
      (up ℤ) a b n hn ≫ φ.f n) h
    simp only [HomologicalComplex.comp_f, HomologicalComplex.ι_mapBifunctorMap_assoc,
      HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp] at this
    exact this
  rw [tensorPairing_μ, tensorPairing_μ, ← Category.assoc, ← Category.assoc]
  exact comp_eq_comp_of_factor _ _ _ _ _ _ _
    (Stacks.Cech.SheafTensorPairing.sheafTensorPairing_naturality_right O ⊤ (F₁.obj.X a)
      (v.hom.f b))
    (Stacks.Cech.SheafTensorPairing.sheafTensorPairing_naturality_left O ⊤ (u.hom.f a)
      (G₂.obj.X b))
    (((Stacks.Cech.ModuleCupProduct.sectionsFunctor O ⊤).map_comp _ _).symm.trans
      ((congrArg (Stacks.Cech.ModuleCupProduct.sectionsFunctor O ⊤).map key).trans
        ((Stacks.Cech.ModuleCupProduct.sectionsFunctor O ⊤).map_comp _ _)))

/-- **[Stacks, Tag 07MC].**  Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` (the short complex `S`) and
`0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` (the short complex `T`) be short exact sequences of bounded below
complexes of `𝒪_X`-modules, `H` a bounded below complex and `γᵢ : Tot(Fᵢ ⊗_{𝒪_X} Gᵢ) ⟶ H` maps of
complexes such that the squares

`γ₁ ∘ Tot(1 ⊗ (G₂ → G₁)) = γ₂ ∘ Tot((F₁ → F₂) ⊗ 1)` and
`γ₂ ∘ Tot(1 ⊗ (G₃ → G₂)) = γ₃ ∘ Tot((F₂ → F₃) ⊗ 1)`

commute.  If Čech cohomology agrees with cohomology for the sheaves `Fᵢᵖ` and `Gⱼ^q`, then for
`a₃ ∈ Hⁿ(X, F₃)` and `b₁ ∈ Hᵐ(X, G₁)`

`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)`  in `H^{n+m+1}(X, H)`.

The source states this for complexes of abelian sheaves and `⊗_𝐙`. That is the case where
`𝒪_X` is the constant sheaf of rings `𝐙_X`: sheaves of `𝐙_X`-modules are the abelian sheaves
(`Stacks.Cech.Hypercohomology.isEquivalence_toSheaf_integerRingSheaf`), and `⊗_{𝐙_X}` is `⊗_𝐙`,
since both are the sheafification of presheaves whose stalks are `Fₓ ⊗_𝐙 Gₓ`. -/
@[stacks 07MC "for complexes of modules over an arbitrary sheaf of commutative rings `𝒪_X` and
`⊗_{𝒪_X}`; the source's abelian sheaves and `⊗_𝐙` are the case `𝒪_X = 𝐙_X`, whose modules are
the abelian sheaves (`Stacks.Cech.Hypercohomology.isEquivalence_toSheaf_integerRingSheaf`) and
whose tensor product is `⊗_𝐙`. `cup` is the cup product of Čech cocycles on a common covering
and `boundary` the connecting map of the long exact cohomology sequence"]
theorem cup_boundary
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact)
    (T : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hT : (toSC T).ShortExact) (H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (γ₁ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor S.X₁.obj T.X₃.obj (sheafTensor O) (up ℤ) ⟶ H.obj)
    (γ₂ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor S.X₂.obj T.X₂.obj (sheafTensor O) (up ℤ) ⟶ H.obj)
    (γ₃ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctor S.X₃.obj T.X₁.obj (sheafTensor O) (up ℤ) ⟶ H.obj)
    (h₁ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctorMap (𝟙 S.X₁.obj) T.g.hom (sheafTensor O) (up ℤ) ≫ γ₁ =
      HomologicalComplex.mapBifunctorMap S.f.hom (𝟙 T.X₂.obj) (sheafTensor O) (up ℤ) ≫ γ₂)
    (h₂ : letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
        inferInstance
      HomologicalComplex.mapBifunctorMap (𝟙 S.X₂.obj) T.f.hom (sheafTensor O) (up ℤ) ≫ γ₂ =
      HomologicalComplex.mapBifunctorMap S.g.hom (𝟙 T.X₁.obj) (sheafTensor O) (up ℤ) ≫ γ₃)
    (hF₁ : ∀ p, CechComputesSheaf O (S.X₁.obj.X p)) (hF₂ : ∀ p, CechComputesSheaf O (S.X₂.obj.X p))
    (hF₃ : ∀ p, CechComputesSheaf O (S.X₃.obj.X p)) (hG₁ : ∀ q, CechComputesSheaf O (T.X₃.obj.X q))
    (hG₂ : ∀ q, CechComputesSheaf O (T.X₂.obj.X q)) (hG₃ : ∀ q, CechComputesSheaf O (T.X₁.obj.X q))
    (n m : ℤ) (a₃ : hypercohomology O S.X₃ n) (b₁ : hypercohomology O T.X₃ m) :
    cup O (cechComputes_of_terms O _ hF₁) (cechComputes_of_terms O _ hG₁) (tensorPairing O γ₁)
        (n + 1) m (n + m + 1) (by omega) (boundary O S hS n (n + 1) rfl a₃) b₁ =
      ((n + 1).negOnePow : ℤ) •
        cup O (cechComputes_of_terms O _ hF₃) (cechComputes_of_terms O _ hG₃) (tensorPairing O γ₃)
          n (m + 1) (n + m + 1) (by omega) a₃ (boundary O T hT m (m + 1) rfl b₁) :=
  cup_boundary_of_pairing O S hS T hT H (tensorPairing O γ₁) (tensorPairing O γ₂)
    (tensorPairing O γ₃) (tensorPairing_square O S.f T.g γ₁ γ₂ h₁)
    (tensorPairing_square O S.g T.f γ₂ γ₃ h₂) hF₁ hF₂ hF₃ hG₁ hG₂ hG₃ n m a₃ b₁

end Stacks.Cech.Hypercohomology
