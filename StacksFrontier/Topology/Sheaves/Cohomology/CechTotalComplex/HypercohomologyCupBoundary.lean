module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyDevissage

/-!
# The cup product and the boundary maps of two short exact sequences

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, let
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` and `0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` be short exact sequences of bounded below
complexes of `𝒪_X`-modules, `H` a bounded below complex, and `γᵢ` pairings of `Fᵢ` and `Gᵢ` into
`H` on sections compatible with the maps of the two sequences.  If Čech cohomology agrees with
cohomology for the sheaves `Fᵢᵖ` and `Gⱼ^q`, then for `a₃ ∈ Hⁿ(X, F₃)` and `b₁ ∈ Hᵐ(X, G₁)`

`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)`  in `H^{n+m+1}(X, H)`.

The proof is the one of [Stacks, Tag 07MC]: both classes are represented by Čech cocycles on a
common covering, computed from a lift `α₂` of a representative of `a₃` and a lift `β₂` of a
representative of `b₁`, and the cochains `γ₁(d(α₂) ∪ β̄₂)` and `(-1)^{n+1} γ₃(ᾱ₂ ∪ d(β₂))`
differ by the coboundary of `γ₂(α₂ ∪ β₂)`.  The hypothesis on the terms of the complexes enters
through `Stacks.Cech.Hypercohomology.cechComputes_of_terms`: Čech cohomology then computes the
cohomology of each of the six complexes.

## Main results

* `Stacks.Cech.Hypercohomology.cup_boundary_of_cechComputes`: the identity, when Čech cohomology
  computes the cohomology of the six complexes.
* `Stacks.Cech.Hypercohomology.cup_boundary_of_pairing`: the identity when Čech cohomology
  agrees with cohomology for the sheaves `Fᵢᵖ` and `Gⱼ^q`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.Cohomology.RightDerivedBoundary
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject)
open Stacks.Cech.CupProduct (tensorModules tensorModulesMap)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-- **A Čech lift of a class of `Hⁿ(X, K₃)`** for a short exact sequence
`0 ⟶ K₁ ⟶ K₂ ⟶ K₃ ⟶ 0` on a covering `𝒰`: a cochain `α₂` of `Tot(Č(𝒰, K₂))` whose image is a
cocycle representing the class, together with a cocycle `α₁` of `Tot(Č(𝒰, K₁))` mapping to
`d(α₂)`. -/
structure CechLift (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (n : ℤ) (a : unitModule _ ⟶ hypercohomology O S.X₃ n) {I : Type u} (U : I → Opens X)
    (hU : ⊤ = ⨆ i, U i) where
  /-- The lift. -/
  α₂ : unitModule _ ⟶ ((cech O U hU).obj S.X₂.obj).X n
  /-- The cocycle mapping to its coboundary. -/
  α₁ : unitModule _ ⟶ ((cech O U hU).obj S.X₁.obj).X (n + 1)
  hα₃ : (α₂ ≫ ((cech O U hU).map S.g.hom).f n) ≫ ((cech O U hU).obj S.X₃.obj).d n (n + 1) = 0
  hα₁ : α₁ ≫ ((cech O U hU).obj S.X₁.obj).d (n + 1) (n + 1 + 1) = 0
  hα : α₁ ≫ ((cech O U hU).map S.f.hom).f (n + 1) = α₂ ≫ ((cech O U hU).obj S.X₂.obj).d n (n + 1)
  hcls : cocycleClass n _ hα₃ ≫ cechClass O U hU S.X₃ n = a

/-- A Čech lift on a covering exists, when Čech cohomology computes the cohomology of `K₁` and
`K₂`. -/
theorem CechLift.exists (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (h₁ : CechComputes O S.X₁) (h₂ : CechComputes O S.X₂)
    (a : unitModule _ ⟶ hypercohomology O S.X₃ n) :
    ∃ (I : Type u) (U : I → Opens X) (hU : ⊤ = ⨆ i, U i), Nonempty (CechLift O S n a U hU) := by
  obtain ⟨I, U, hU, α₂, α₁, hα₃, hα₁, hα, hcls⟩ := exists_cechLift O S hS n h₁ h₂ a
  exact ⟨I, U, hU, ⟨⟨α₂, α₁, hα₃, hα₁, hα, hcls⟩⟩⟩

/-- A Čech lift refined along a refinement of coverings. -/
def CechLift.refine {S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))}
    {n : ℤ} {a : unitModule _ ⟶ hypercohomology O S.X₃ n} {I : Type u} {U : I → Opens X}
    {hU : ⊤ = ⨆ i, U i} (L : CechLift O S n a U hU) {J : Type u} (V : J → Opens X)
    (hV : ⊤ = ⨆ j, V j) (c : J → I) (hc : ∀ j, V j ≤ U (c j)) : CechLift O S n a V hV :=
  let ρ := Stacks.Cech.Refinement.cechRefinement O U hU V hV c hc
  have nat : ∀ {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))} (f : K ⟶ L) (k : ℤ),
      ((cech O U hU).map f.hom).f k ≫ (ρ.app L.obj).f k =
        (ρ.app K.obj).f k ≫ ((cech O V hV).map f.hom).f k := fun f k => by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, ρ.naturality]
  have hα₃' : ((L.α₂ ≫ ((cech O U hU).map S.g.hom).f n) ≫ (ρ.app S.X₃.obj).f n) ≫
      ((cech O V hV).obj S.X₃.obj).d n (n + 1) = 0 := by
    rw [Category.assoc, (ρ.app S.X₃.obj).comm, ← Category.assoc, L.hα₃, zero_comp]
  have he : (L.α₂ ≫ (ρ.app S.X₂.obj).f n) ≫ ((cech O V hV).map S.g.hom).f n =
      (L.α₂ ≫ ((cech O U hU).map S.g.hom).f n) ≫ (ρ.app S.X₃.obj).f n := by
    rw [Category.assoc, Category.assoc, nat]
  { α₂ := L.α₂ ≫ (ρ.app S.X₂.obj).f n
    α₁ := L.α₁ ≫ (ρ.app S.X₁.obj).f (n + 1)
    hα₃ := by rw [he]; exact hα₃'
    hα₁ := by rw [Category.assoc, (ρ.app S.X₁.obj).comm, ← Category.assoc, L.hα₁, zero_comp]
    hα := by
      rw [Category.assoc, ← nat, ← Category.assoc, L.hα, Category.assoc, Category.assoc,
        (ρ.app S.X₂.obj).comm]
    hcls := by
      rw [cocycleClass_congr n he _ hα₃', ← cocycleClass_comp_homologyMap _ n _ L.hα₃,
        Category.assoc, cechClass_refinement, L.hcls] }

/-- The class of a cocycle as an element. -/
theorem toMor_cocycleClass_apply
    {K : CochainComplex (ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)) ℤ}
    (n : ℤ) (x : unitModule _ ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) :
    toMor ((cocycleClass n x hx) (1 : SectionRing (ringSheaf O) ⊤)) = cocycleClass n x hx :=
  toMor_apply _

/-- The boundary of a class with a Čech lift is the class of the cocycle `α₁` of the lift. -/
private theorem boundary_eq_cechClass_cocycleClass
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (a : hypercohomology O S.X₃ n) {I : Type u}
    {U : I → Opens X} {hU : ⊤ = ⨆ i, U i} (L : CechLift O S n (toMor a) U hU) :
    boundary O S hS n (n + 1) rfl a = cechClass O U hU S.X₁ (n + 1)
      ((cocycleClass (n + 1) L.α₁ L.hα₁) (1 : SectionRing (ringSheaf O) ⊤)) := by
  rw [← ConcreteCategory.comp_apply, cechClass_boundary O U hU S hS n L.α₂ L.α₁ L.hα₃ L.hα₁ L.hα,
    ← Category.assoc, L.hcls, toMor_comp, toMor_apply_one]

/-- A class with a Čech lift is the class of the cocycle image of `α₂` of the lift. -/
private theorem eq_cechClass_cocycleClass
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (n : ℤ) (a : hypercohomology O S.X₃ n) {I : Type u} {U : I → Opens X}
    {hU : ⊤ = ⨆ i, U i} (L : CechLift O S n (toMor a) U hU) :
    a = cechClass O U hU S.X₃ n ((cocycleClass n _ L.hα₃) (1 : SectionRing (ringSheaf O) ⊤)) := by
  rw [← ConcreteCategory.comp_apply, L.hcls, toMor_apply_one]

/-- The cup product of two classes with Čech representatives on one covering is the class of the
Čech cup product of the representatives. -/
private theorem cup_eq_of_eq_cechClass
    {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) {I : Type u} {U : I → Opens X} {hU : ⊤ = ⨆ i, U i}
    {a : hypercohomology O F p} {b : hypercohomology O G q}
    {x : ((cech O U hU).obj F.obj).homology p} {y : ((cech O U hU).obj G.obj).homology q}
    (ha : a = cechClass O U hU F p x) (hb : b = cechClass O U hU G q y) :
    cup O hF hG γ p q t ht a b =
      (cechCupClass O U hU γ p q t ht (toMor x) (toMor y) ≫ cechClass O U hU H t)
        (1 : SectionRing (ringSheaf O) ⊤) := by
  subst ha hb
  exact cup_eq O U hU hF hG γ p q t ht x y

/-- **[Stacks, Tag 07MC], with Čech cohomology computing the cohomology of the six complexes.**
Let `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` (the short complex `S`) and `0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` (the short complex
`T`) be short exact sequences of bounded below complexes of `𝒪_X`-modules, `H` a bounded below
complex and `γ₁`, `γ₂`, `γ₃` pairings of `(F₁, G₁)`, `(F₂, G₂)`, `(F₃, G₃)` into `H` compatible
with the maps of the two sequences: `γ₁ ∘ (1 ⊗ (G₂ → G₁)) = γ₂ ∘ ((F₁ → F₂) ⊗ 1)` and
`γ₂ ∘ (1 ⊗ (G₃ → G₂)) = γ₃ ∘ ((F₂ → F₃) ⊗ 1)`.  Then for `a₃ ∈ Hⁿ(X, F₃)` and `b₁ ∈ Hᵐ(X, G₁)`,

`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)`  in `H^{n+m+1}(X, H)`. -/
theorem cup_boundary_of_cechComputes
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact)
    (T : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hT : (toSC T).ShortExact) (H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (γ₁ : Pairing O S.X₁ T.X₃ H) (γ₂ : Pairing O S.X₂ T.X₂ H) (γ₃ : Pairing O S.X₃ T.X₁ H)
    (h₁ : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj S.X₁.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map T.g.hom).f b) ≫ γ₁.μ a b n hn =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map S.f.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj T.X₂.obj).X b) ≫ γ₂.μ a b n hn)
    (h₂ : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj S.X₂.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map T.f.hom).f b) ≫ γ₂.μ a b n hn =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map S.g.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj T.X₁.obj).X b) ≫ γ₃.μ a b n hn)
    (hF₁ : CechComputes O S.X₁) (hF₂ : CechComputes O S.X₂) (hF₃ : CechComputes O S.X₃)
    (hG₁ : CechComputes O T.X₃) (hG₂ : CechComputes O T.X₂) (hG₃ : CechComputes O T.X₁)
    (n m : ℤ) (a₃ : hypercohomology O S.X₃ n) (b₁ : hypercohomology O T.X₃ m) :
    cup O hF₁ hG₁ γ₁ (n + 1) m (n + m + 1) (by omega) (boundary O S hS n (n + 1) rfl a₃) b₁ =
      ((n + 1).negOnePow : ℤ) •
        cup O hF₃ hG₃ γ₃ n (m + 1) (n + m + 1) (by omega) a₃
          (boundary O T hT m (m + 1) rfl b₁) := by
  obtain ⟨I, U, hU, ⟨La⟩⟩ := CechLift.exists O S hS n hF₁ hF₂ (toMor a₃)
  obtain ⟨I', U', hU', ⟨Lb⟩⟩ := CechLift.exists O T hT m hG₃ hG₂ (toMor b₁)
  have hW := iSup_inf_eq_top U hU U' hU'
  let A := La.refine O _ hW Prod.fst (fun _ => inf_le_left)
  let B := Lb.refine O _ hW Prod.snd (fun _ => inf_le_right)
  -- the identity of cohomology classes of the total Čech complex of `H`
  have hcore := Stacks.CupProduct.gamma_cup_boundary_homologyClass
    (tensorModules (SectionRing (ringSheaf O) ⊤)) ((cech O _ hW).map S.f.hom)
    ((cech O _ hW).map S.g.hom) ((cech O _ hW).map T.f.hom) ((cech O _ hW).map T.g.hom)
    (cechCup O _ hW γ₁) (cechCup O _ hW γ₂) (cechCup O _ hW γ₃)
    (cechCup_naturality O _ hW S.f T.g γ₁ γ₂ h₁) (cechCup_naturality O _ hW S.g T.f γ₂ γ₃ h₂)
    n m A.α₂ B.α₂ A.α₁ A.hα B.α₁ B.hα
    (Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero _ _ _ _ (n + 1) m _ _ _ _ A.hα₁ B.hα₃)
    (Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero _ _ _ _ n (m + 1) _ _ _ _ A.hα₃ B.hα₁)
  have L := cup_eq_of_eq_cechClass O hF₁ hG₁ γ₁ (n + 1) m (n + m + 1) (by omega)
    (boundary_eq_cechClass_cocycleClass O S hS n _ A) (eq_cechClass_cocycleClass O T m _ B)
  have R := cup_eq_of_eq_cechClass O hF₃ hG₃ γ₃ n (m + 1) (n + m + 1) (by omega)
    (eq_cechClass_cocycleClass O S n _ A) (boundary_eq_cechClass_cocycleClass O T hT m _ B)
  refine L.trans (Eq.trans ?_ (congrArg (fun z => ((n + 1).negOnePow : ℤ) • z) R.symm))
  rw [toMor_cocycleClass_apply, toMor_cocycleClass_apply,
    toMor_cocycleClass_apply, toMor_cocycleClass_apply, cechCupClass_eq, cechCupClass_eq]
  dsimp only [cocycleClass]
  rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, ← Category.assoc
    (HomologicalComplex.liftCycles _ _ _ _ _), hcore, Preadditive.zsmul_comp,
    Preadditive.comp_zsmul]
  rfl


/-- **The identity of Tag 07MC for pairings on sections.**  For short exact sequences
`0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` and `0 ⟶ G₃ ⟶ G₂ ⟶ G₁ ⟶ 0` of bounded below complexes of `𝒪_X`-modules
and pairings `γᵢ` of `(Fᵢ, Gᵢ)` into `H` on sections compatible with the maps of the two
sequences, if Čech cohomology agrees with cohomology for the sheaves `Fᵢᵖ` and `Gⱼ^q`, then
`γ₁(∂a₃ ∪ b₁) = (-1)^{n+1} γ₃(a₃ ∪ ∂b₁)` in `H^{n+m+1}(X, H)`. -/
theorem cup_boundary_of_pairing
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact)
    (T : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hT : (toSC T).ShortExact) (H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (γ₁ : Pairing O S.X₁ T.X₃ H) (γ₂ : Pairing O S.X₂ T.X₂ H) (γ₃ : Pairing O S.X₃ T.X₁ H)
    (h₁ : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj S.X₁.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map T.g.hom).f b) ≫ γ₁.μ a b n hn =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map S.f.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj T.X₂.obj).X b) ≫ γ₂.μ a b n hn)
    (h₂ : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj S.X₂.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map T.f.hom).f b) ≫ γ₂.μ a b n hn =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map S.g.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj T.X₁.obj).X b) ≫ γ₃.μ a b n hn)
    (hF₁ : ∀ p, CechComputesSheaf O (S.X₁.obj.X p)) (hF₂ : ∀ p, CechComputesSheaf O (S.X₂.obj.X p))
    (hF₃ : ∀ p, CechComputesSheaf O (S.X₃.obj.X p)) (hG₁ : ∀ q, CechComputesSheaf O (T.X₃.obj.X q))
    (hG₂ : ∀ q, CechComputesSheaf O (T.X₂.obj.X q)) (hG₃ : ∀ q, CechComputesSheaf O (T.X₁.obj.X q))
    (n m : ℤ) (a₃ : hypercohomology O S.X₃ n) (b₁ : hypercohomology O T.X₃ m) :
    cup O (cechComputes_of_terms O _ hF₁) (cechComputes_of_terms O _ hG₁) γ₁ (n + 1) m (n + m + 1)
        (by omega) (boundary O S hS n (n + 1) rfl a₃) b₁ =
      ((n + 1).negOnePow : ℤ) •
        cup O (cechComputes_of_terms O _ hF₃) (cechComputes_of_terms O _ hG₃) γ₃ n (m + 1)
          (n + m + 1) (by omega) a₃ (boundary O T hT m (m + 1) rfl b₁) :=
  cup_boundary_of_cechComputes O S hS T hT H γ₁ γ₂ γ₃ h₁ h₂ _ (cechComputes_of_terms O _ hF₂) _ _
    (cechComputes_of_terms O _ hG₂) _ n m a₃ b₁

end Stacks.Cech.Hypercohomology
