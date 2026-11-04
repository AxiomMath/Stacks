module

public import Mathlib.CategoryTheory.Sites.Descent.DescentDataPrime
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RankDecomposition
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcEffectiveUnconditional
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.StandardAffineFamily
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.PicardScheme.BaseChangePullback
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceLeftExactness
public import StacksFrontier.AlgebraicGeometry.PicardScheme.SectionPullbackInvertible
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.SieveToFamily
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison

/-!
# Gluing and fpqc descent tools for the split Picard sequence

The general tools behind the split exact Picard sequence of a morphism with a section: algebra
of `pullHom`, gluing of isomorphisms of pullbacks along a family, normalised descent data built
from a family of objects, effectivity of fpqc descent read on representatives, and descent of
invertibility along an fpqc covering (`Stacks.Picard.isInvertible_of_pullback_fpqcCover`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open CategoryTheory.Pseudofunctor CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v w z u' v'

namespace Stacks.Limits

/-- A chosen pullback of the two projections `h₁₂.pullback ⟶ X₂` and `h₂₃.pullback ⟶ X₂` is a
chosen wide pullback of three morphisms `f₁`, `f₂`, `f₃` with common target. -/
def chosenPullback₃OfChosenPullback {C : Type*} [Category C]
    {X₁ X₂ X₃ Y : C} {f₁ : X₁ ⟶ Y} {f₂ : X₂ ⟶ Y} {f₃ : X₃ ⟶ Y}
    (h₁₂ : ChosenPullback f₁ f₂) (h₂₃ : ChosenPullback f₂ f₃) (h₁₃ : ChosenPullback f₁ f₃)
    (d : ChosenPullback h₁₂.p₂ h₂₃.p₁) : ChosenPullback₃ h₁₂ h₂₃ h₁₃ := by
  refine { chosenPullback := d, l := Classical.choice ?_ }
  refine ChosenPullback.LiftStruct.nonempty ?_ ?_
  · calc (d.p₁ ≫ h₁₂.p₁) ≫ f₁ = d.p₁ ≫ h₁₂.p₂ ≫ f₂ := by
          rw [Category.assoc, h₁₂.hp₁, h₁₂.hp₂]
      _ = d.p₂ ≫ h₂₃.p₁ ≫ f₂ := by rw [← Category.assoc, d.condition, Category.assoc]
      _ = (d.p₂ ≫ h₂₃.p₂) ≫ f₃ := by rw [Category.assoc, h₂₃.hp₁, h₂₃.hp₂]
  · rw [Category.assoc, h₁₂.hp₁]

end Stacks.Limits

namespace Stacks.Picard

/-! ### generic pullHom algebra -/

/-- Restricting a composite of two restrictions-compatible homomorphisms is the composite of
their restrictions. -/
theorem pullHom_comp'
    {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {X₁ X₂ X₃ Y Z : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {M₃ : F.obj (.mk (op X₃))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂} {f₃ : Y ⟶ X₃}
    (a : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (b : (F.map f₂.op.toLoc).toFunctor.obj M₂ ⟶ (F.map f₃.op.toLoc).toFunctor.obj M₃)
    (g : Z ⟶ Y) (gf₁ : Z ⟶ X₁) (gf₂ : Z ⟶ X₂) (gf₃ : Z ⟶ X₃)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) (h₃ : g ≫ f₃ = gf₃) :
    pullHom (a ≫ b) g gf₁ gf₃ h₁ h₃ =
      pullHom a g gf₁ gf₂ h₁ h₂ ≫ pullHom b g gf₂ gf₃ h₂ h₃ := by
  simp [pullHom, Functor.map_comp, Category.assoc, ← reassoc_of% Cat.Hom₂.comp_app]

/-- Restricting an identity gives an identity. -/
theorem pullHom_id'
    {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {X Y Z : C} (M : F.obj (.mk (op X)))
    (f : Y ⟶ X) (g : Z ⟶ Y) (gf : Z ⟶ X) (h : g ≫ f = gf) :
    pullHom (𝟙 ((F.map f.op.toLoc).toFunctor.obj M)) g gf gf h h = 𝟙 _ := by
  simp [pullHom, ← Cat.Hom₂.comp_app]

/-- Restricting a restriction along two morphisms is restricting along a morphism equal to
their composite. -/
theorem pullHom_pullHom_of_eq {C : Type*} [Category C]
    {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat} {X₁ X₂ Y Z Z' : C}
    {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (F.map f₁.op.toLoc).toFunctor.obj M₁ ⟶ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Z ⟶ Y) (gf₁ : Z ⟶ X₁) (gf₂ : Z ⟶ X₂) (hgf₁ : g ≫ f₁ = gf₁) (hgf₂ : g ≫ f₂ = gf₂)
    (g' : Z' ⟶ Z) (k : Z' ⟶ Y) (hk : g' ≫ g = k) (kf₁ : Z' ⟶ X₁) (kf₂ : Z' ⟶ X₂)
    (h₁ : g' ≫ gf₁ = kf₁) (h₂ : g' ≫ gf₂ = kf₂) (hk₁ : k ≫ f₁ = kf₁) (hk₂ : k ≫ f₂ = kf₂) :
    pullHom (pullHom φ g gf₁ gf₂ hgf₁ hgf₂) g' kf₁ kf₂ h₁ h₂ = pullHom φ k kf₁ kf₂ hk₁ hk₂ := by
  subst hk
  exact pullHom_pullHom φ g gf₁ gf₂ g' kf₁ kf₂ hgf₁ hgf₂ h₁ h₂

/-- The restriction of the forward direction of an isomorphism is a left inverse of the
restriction of its inverse. -/
theorem pullHom_hom_comp_pullHom_inv
    {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {X₁ X₂ Y Z : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Z ⟶ Y) (gf₁ : Z ⟶ X₁) (gf₂ : Z ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom e.hom g gf₁ gf₂ h₁ h₂ ≫ pullHom e.inv g gf₂ gf₁ h₂ h₁ = 𝟙 _ := by
  rw [← pullHom_comp' e.hom e.inv g gf₁ gf₂ gf₁ h₁ h₂ h₁, e.hom_inv_id, pullHom_id']

/-- The restriction of the inverse of an isomorphism is a left inverse of the restriction of
its forward direction. -/
theorem pullHom_inv_comp_pullHom_hom
    {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {X₁ X₂ Y Z : C} {M₁ : F.obj (.mk (op X₁))} {M₂ : F.obj (.mk (op X₂))}
    {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (e : (F.map f₁.op.toLoc).toFunctor.obj M₁ ≅ (F.map f₂.op.toLoc).toFunctor.obj M₂)
    (g : Z ⟶ Y) (gf₁ : Z ⟶ X₁) (gf₂ : Z ⟶ X₂) (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    pullHom e.inv g gf₂ gf₁ h₂ h₁ ≫ pullHom e.hom g gf₁ gf₂ h₁ h₂ = 𝟙 _ := by
  exact pullHom_hom_comp_pullHom_inv e.symm g gf₂ gf₁ h₂ h₁

/-! ### gluing homomorphisms along a family -/

/-- A family of morphisms between the pullbacks of `M` and `N` along a family `u i : Z i ⟶ T`
that agree after every further pullback is the pullback of a morphism `M ⟶ N`, as soon as
pulling morphisms back to the family is bijective. -/
theorem exists_map_eq_of_pullHom_eq
    {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {T : C} {Z : ι → C} (u : ∀ i, Z i ⟶ T) {M N : F.obj (.mk (op T))}
    (hb : Function.Bijective ((F.toDescentData u).map : (M ⟶ N) → _))
    (ψ : ∀ i, (F.map (u i).op.toLoc).toFunctor.obj M ⟶ (F.map (u i).op.toLoc).toFunctor.obj N)
    (h : ∀ ⦃Y : C⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (a₁ : Y ⟶ Z i₁) (a₂ : Y ⟶ Z i₂)
      (ha₁ : a₁ ≫ u i₁ = q) (ha₂ : a₂ ≫ u i₂ = q),
      pullHom (ψ i₁) a₁ q q ha₁ ha₁ = pullHom (ψ i₂) a₂ q q ha₂ ha₂) :
    ∃ φ : M ⟶ N, ∀ i, (F.map (u i).op.toLoc).toFunctor.map φ = ψ i := by
  obtain ⟨φ, hφ⟩ := hb.surjective
    (Pseudofunctor.DescentData.subtypeCompatibleHomEquiv F u
      ⟨ψ, Stacks.Descent.compatible_presheafHom u ψ h⟩)
  exact ⟨φ, fun i => congrFun (congrArg Pseudofunctor.DescentData.Hom.hom hφ) i⟩

/-- A family of isomorphisms between the pullbacks of `M` and `N` along a family `u i : Z i ⟶ T`
whose members agree after every further pullback exhibits `M` and `N` as isomorphic, as soon as
pulling morphisms back to the family is bijective on the four relevant hom-sets. -/
theorem nonempty_iso_of_pullHom_hom_eq
    {C : Type*} [Category C] {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {T : C} {Z : ι → C} (u : ∀ i, Z i ⟶ T) {M N : F.obj (.mk (op T))}
    (hMN : Function.Bijective ((F.toDescentData u).map : (M ⟶ N) → _))
    (hNM : Function.Bijective ((F.toDescentData u).map : (N ⟶ M) → _))
    (hMM : Function.Bijective ((F.toDescentData u).map : (M ⟶ M) → _))
    (hNN : Function.Bijective ((F.toDescentData u).map : (N ⟶ N) → _))
    (ψ : ∀ i, (F.map (u i).op.toLoc).toFunctor.obj M ≅ (F.map (u i).op.toLoc).toFunctor.obj N)
    (h : ∀ ⦃Y : C⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (a₁ : Y ⟶ Z i₁) (a₂ : Y ⟶ Z i₂)
      (ha₁ : a₁ ≫ u i₁ = q) (ha₂ : a₂ ≫ u i₂ = q),
      pullHom (ψ i₁).hom a₁ q q ha₁ ha₁ = pullHom (ψ i₂).hom a₂ q q ha₂ ha₂) :
    Nonempty (M ≅ N) := by
  have hinv : ∀ ⦃Y : C⦄ (q : Y ⟶ T) ⦃i₁ i₂ : ι⦄ (a₁ : Y ⟶ Z i₁) (a₂ : Y ⟶ Z i₂)
      (ha₁ : a₁ ≫ u i₁ = q) (ha₂ : a₂ ≫ u i₂ = q),
      pullHom (ψ i₁).inv a₁ q q ha₁ ha₁ = pullHom (ψ i₂).inv a₂ q q ha₂ ha₂ := by
    intro Y q i₁ i₂ a₁ a₂ ha₁ ha₂
    calc pullHom (ψ i₁).inv a₁ q q ha₁ ha₁
        = pullHom (ψ i₁).inv a₁ q q ha₁ ha₁ ≫
            pullHom (ψ i₂).hom a₂ q q ha₂ ha₂ ≫ pullHom (ψ i₂).inv a₂ q q ha₂ ha₂ := by
          rw [pullHom_hom_comp_pullHom_inv (ψ i₂) a₂ q q ha₂ ha₂, Category.comp_id]
      _ = (pullHom (ψ i₁).inv a₁ q q ha₁ ha₁ ≫ pullHom (ψ i₁).hom a₁ q q ha₁ ha₁) ≫
            pullHom (ψ i₂).inv a₂ q q ha₂ ha₂ := by
          rw [Category.assoc, h q a₂ a₁ ha₂ ha₁]
      _ = pullHom (ψ i₂).inv a₂ q q ha₂ ha₂ := by
          rw [pullHom_inv_comp_pullHom_hom (ψ i₁) a₁ q q ha₁ ha₁, Category.id_comp]
  obtain ⟨φ, hφ⟩ := exists_map_eq_of_pullHom_eq u hMN (fun i => (ψ i).hom) h
  obtain ⟨φ', hφ'⟩ := exists_map_eq_of_pullHom_eq u hNM (fun i => (ψ i).inv) hinv
  refine ⟨⟨φ, φ', hMM.injective ?_, hNN.injective ?_⟩⟩
  · refine Pseudofunctor.DescentData.hom_ext fun i => ?_
    show (F.map (u i).op.toLoc).toFunctor.map (φ ≫ φ') =
      (F.map (u i).op.toLoc).toFunctor.map (𝟙 M)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hφ i, hφ' i,
      Iso.hom_inv_id]
  · refine Pseudofunctor.DescentData.hom_ext fun i => ?_
    show (F.map (u i).op.toLoc).toFunctor.map (φ' ≫ φ) =
      (F.map (u i).op.toLoc).toFunctor.map (𝟙 N)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id, hφ i, hφ' i,
      Iso.inv_hom_id]


/-- An invertible module on a scheme is finite locally free of rank one. -/
private theorem isFiniteLocallyFreeOfRank_one_of_stacksIsInvertible {Z : Scheme.{u}}
    (L : Z.Modules) (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
  Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible Z L
    ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Z.presheaf _ _).mp hL)

/-- A module on a scheme that is finite locally free of rank one is invertible. -/
private theorem stacksIsInvertible_of_isFiniteLocallyFreeOfRank_one {Z : Scheme.{u}}
    (L : Z.Modules) (hL : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1) :
    Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L :=
  (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
    Z.presheaf _ _).mpr (Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one Z L hL)

/-- An invertible module on a scheme is quasi-coherent: it is finite locally free of rank one. -/
theorem isQuasicoherent_of_isInvertible {Z : Scheme.{u}} (L : Z.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 L) :
    L.IsQuasicoherent := by
  have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    isFiniteLocallyFreeOfRank_one_of_stacksIsInvertible L hL
  have h2 : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  obtain ⟨c, hc, _⟩ := h2.exists_isFiniteLocallyFreeData
  have : c.IsLocallyFreeData := hc
  exact c.quasiCoherentData.isQuasicoherent

/-- Pulling morphisms of quasi-coherent modules back to an fpqc covering family is bijective
onto the morphisms of the associated descent data. -/
theorem bijective_toDescentData_map_of_fpqc {Z : Scheme.{u}} {ι : Type*} {Y : ι → Scheme.{u}}
    (u : ∀ i, Y i ⟶ Z) (hu : Presieve.ofArrows Y u ∈ Scheme.fpqcPrecoverage.{u} Z)
    (M N : Z.Modules) (hM : M.IsQuasicoherent) (hN : N.IsQuasicoherent) :
    Function.Bijective ((modulePullbackPseudofunctor.toDescentData u).map : (M ⟶ N) → _) :=
  (Pseudofunctor.bijective_toDescentData_map_iff (F := modulePullbackPseudofunctor) u M N).mpr
    (@isSheafFor_presheafHom_fpqc Z M N hM hN ι Y u hu)

/-- A Picard class whose pullback along `g` vanishes has a representative whose pullback along
`g` is isomorphic to the pullback of the structure sheaf, in the spelling of the pullback
pseudofunctor. -/
theorem nonempty_pullHomIso_of_schemePullbackClass_eq_zero {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (x : ofScheme Z) (hx : schemePullbackClass g x = 0) :
    Nonempty ((modulePullbackPseudofunctor.map g.op.toLoc).toFunctor.obj
        (picardRepresentative Z.toRingedSpace x).obj ≅
      (modulePullbackPseudofunctor.map g.op.toLoc).toFunctor.obj
        (SheafOfModules.unit Z.ringCatSheaf)) :=
  ((schemePullbackClass_eq_zero_iff_nonempty_iso_unit g x).1 hx).map
    (fun e => e ≪≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).symm)

open Pseudofunctor.LocallyDiscreteOpToCat in
/-- Restriction along a section of a morphism with invariant structure sheaf is bijective on the
homomorphisms between the pullbacks of two invertible modules, in the spelling of the pullback
pseudofunctor and with the composites with the section named. -/
theorem bijective_pullHom_section' {Y Z₁ Z₂ V : Scheme.{u}} (p : Y ⟶ Z₁) (q : Y ⟶ Z₂)
    (f' : Y ⟶ V) (s : V ⟶ Y) (hs : s ≫ f' = 𝟙 V) (hc : IsIso f'.toLRSHom.toHom.c)
    (L₁ : Z₁.Modules) (L₂ : Z₂.Modules)
    (h₁ : Stacks.SheafOfModules.IsInvertible Z₁.presheaf Z₁.ringCatSheaf.2 L₁)
    (h₂ : Stacks.SheafOfModules.IsInvertible Z₂.presheaf Z₂.ringCatSheaf.2 L₂)
    (e : (modulePullbackPseudofunctor.map p.op.toLoc).toFunctor.obj L₁ ≅
      (modulePullbackPseudofunctor.map q.op.toLoc).toFunctor.obj L₂)
    (k₁ : V ⟶ Z₁) (k₂ : V ⟶ Z₂) (hk₁ : s ≫ p = k₁) (hk₂ : s ≫ q = k₂) :
    Function.Bijective
      (fun a : (modulePullbackPseudofunctor.map p.op.toLoc).toFunctor.obj L₁ ⟶
        (modulePullbackPseudofunctor.map q.op.toLoc).toFunctor.obj L₂ =>
          pullHom a s k₁ k₂ hk₁ hk₂) := by
  subst hk₁
  subst hk₂
  have := hc
  have := h₁
  have := h₂
  exact bijective_pullHom_section p q f' s hs L₁ L₂ e

/-! ### Normalised descent data from a family of objects -/



section

variable {C : Type u} [Category.{v} C]
  {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}

variable {D : Type w} [Category.{z} D]
  (P Q : D ⥤ C) (s : P ⟶ Q)
  {I : Type*} {T : D} {U : I → D} (g : ∀ i, U i ⟶ T)
  (L : ∀ i, F.obj (.mk (.op (Q.obj (U i)))))
  (N : F.obj (.mk (.op (P.obj T))))
  (α : ∀ i, (F.map (s.app (U i)).op.toLoc).toFunctor.obj (L i) ≅
    (F.map (P.map (g i)).op.toLoc).toFunctor.obj N)

/-- The comparison, over an object `V` mapping to two members of the family, of the pullbacks
of their objects after restriction along the natural transformation `s`: the two trivialisations
`α` are composed through the common object `N`. -/
def normalizedHomOnBase {V : D} (q : V ⟶ T) {i j : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    (F.map (s.app V ≫ Q.map a).op.toLoc).toFunctor.obj (L i) ⟶
      (F.map (s.app V ≫ Q.map b).op.toLoc).toFunctor.obj (L j) :=
  pullHom (α i).hom (P.map a) (s.app V ≫ Q.map a) (P.map q)
    (s.naturality a) (by rw [← P.map_comp, ha]) ≫
  pullHom (α j).inv (P.map b) (P.map q) (s.app V ≫ Q.map b)
    (by rw [← P.map_comp, hb]) (s.naturality b)

/-- The comparison of a member with itself is the identity. -/
theorem normalizedHomOnBase_self {V : D} (q : V ⟶ T) {i : I}
    (a : V ⟶ U i) (ha : a ≫ g i = q) :
    normalizedHomOnBase P Q s g L N α q a a ha ha = 𝟙 _ := by
  unfold normalizedHomOnBase
  rw [← pullHom_comp', Iso.hom_inv_id, pullHom_id']

/-- The comparisons compose. -/
theorem normalizedHomOnBase_comp {V : D} (q : V ⟶ T) {i j k : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (c : V ⟶ U k)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) (hc : c ≫ g k = q) :
    normalizedHomOnBase P Q s g L N α q a b ha hb ≫
      normalizedHomOnBase P Q s g L N α q b c hb hc =
      normalizedHomOnBase P Q s g L N α q a c ha hc := by
  unfold normalizedHomOnBase
  simp only [Category.assoc]
  rw [← Category.assoc (pullHom (α j).inv _ _ _ _ _), ← pullHom_comp',
    Iso.inv_hom_id, pullHom_id', Category.id_comp]

/-- The comparisons are compatible with further restriction. -/
theorem normalizedHomOnBase_pull {V W : D} (r : W ⟶ V)
    (q : V ⟶ T) {i j : I} (a : V ⟶ U i) (b : V ⟶ U j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    pullHom (normalizedHomOnBase P Q s g L N α q a b ha hb) (P.map r)
      (s.app W ≫ Q.map (r ≫ a)) (s.app W ≫ Q.map (r ≫ b))
      (by rw [Functor.map_comp, ← Category.assoc, s.naturality, Category.assoc])
      (by rw [Functor.map_comp, ← Category.assoc, s.naturality, Category.assoc]) =
      normalizedHomOnBase P Q s g L N α (r ≫ q) (r ≫ a) (r ≫ b)
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  unfold normalizedHomOnBase
  rw [pullHom_comp' _ _ _ _ (P.map (r ≫ q)) _ _ (by rw [P.map_comp])]
  simp only [pullHom_pullHom, ← Functor.map_comp]

variable (β : ∀ {V : D} (q : V ⟶ T) {i j : I}
  (a : V ⟶ U i) (b : V ⟶ U j), a ≫ g i = q → b ≫ g j = q →
  Function.Bijective (fun φ :
    (F.map (Q.map a).op.toLoc).toFunctor.obj (L i) ⟶
      (F.map (Q.map b).op.toLoc).toFunctor.obj (L j) =>
    pullHom φ (s.app V) (s.app V ≫ Q.map a) (s.app V ≫ Q.map b) rfl rfl))

/-- **The normalised comparison upstairs.** The unique homomorphism of the pullbacks of the
objects of two members of the family whose restriction along `s` is the comparison
`Stacks.Picard.normalizedHomOnBase` built from the trivialisations `α`. -/
noncomputable def normalizedHom {V : D} (q : V ⟶ T) {i j : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    (F.map (Q.map a).op.toLoc).toFunctor.obj (L i) ⟶
      (F.map (Q.map b).op.toLoc).toFunctor.obj (L j) :=
  (β q a b ha hb).surjective (normalizedHomOnBase P Q s g L N α q a b ha hb)
    |>.choose

/-- The normalised comparison restricts along `s` to the comparison it was normalised by. -/
theorem normalizedHom_spec {V : D} (q : V ⟶ T) {i j : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    pullHom (normalizedHom P Q s g L N α β q a b ha hb)
      (s.app V) (s.app V ≫ Q.map a) (s.app V ≫ Q.map b) rfl rfl =
      normalizedHomOnBase P Q s g L N α q a b ha hb :=
  (β q a b ha hb).surjective (normalizedHomOnBase P Q s g L N α q a b ha hb)
    |>.choose_spec

/-- The normalised comparison of a member with itself is the identity. -/
theorem normalizedHom_self {V : D} (q : V ⟶ T) {i : I}
    (a : V ⟶ U i) (ha : a ≫ g i = q) :
    normalizedHom P Q s g L N α β q a a ha ha = 𝟙 _ := by
  apply (β q a a ha ha).injective
  dsimp only
  rw [normalizedHom_spec, normalizedHomOnBase_self, pullHom_id']

/-- The normalised comparisons compose. -/
theorem normalizedHom_comp {V : D} (q : V ⟶ T) {i j k : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (c : V ⟶ U k)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) (hc : c ≫ g k = q) :
    normalizedHom P Q s g L N α β q a b ha hb ≫
      normalizedHom P Q s g L N α β q b c hb hc =
      normalizedHom P Q s g L N α β q a c ha hc := by
  apply (β q a c ha hc).injective
  dsimp only
  rw [pullHom_comp' _ _ _ _ (s.app V ≫ Q.map b) _ rfl rfl rfl]
  simp only [normalizedHom_spec, normalizedHomOnBase_comp]

/-- The normalised comparisons are compatible with further restriction, so they are the
transition morphisms of a descent datum. -/
theorem normalizedHom_pull {V W : D} (r : W ⟶ V)
    (q : V ⟶ T) {i j : I} (a : V ⟶ U i) (b : V ⟶ U j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) :
    pullHom (normalizedHom P Q s g L N α β q a b ha hb) (Q.map r)
      (Q.map (r ≫ a)) (Q.map (r ≫ b)) (by rw [Q.map_comp]) (by rw [Q.map_comp]) =
      normalizedHom P Q s g L N α β (r ≫ q) (r ≫ a) (r ≫ b)
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  apply (β (r ≫ q) (r ≫ a) (r ≫ b)
    (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb])).injective
  simp only [pullHom_pullHom, normalizedHom_spec]
  rw [← normalizedHomOnBase_pull P Q s g L N α r q a b ha hb,
    ← normalizedHom_spec P Q s g L N α β q a b ha hb, pullHom_pullHom]
  congr 1
  exact (s.naturality r).symm

end

section

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  (Q : D ⥤ C)

/-- The image under a functor of a chosen fibre product, when the functor carries the square to
a fibre-product square. -/
@[reducible] noncomputable def mapChosenPullback {U V T : D} {a : U ⟶ T} {b : V ⟶ T}
    (c : ChosenPullback a b)
    (h : IsPullback (Q.map c.p₁) (Q.map c.p₂) (Q.map a) (Q.map b)) :
    ChosenPullback (Q.map a) (Q.map b) where
  pullback := Q.obj c.pullback
  p₁ := Q.map c.p₁
  p₂ := Q.map c.p₂
  condition := h.w
  isLimit := h.isLimit
  p := Q.map c.p
  hp₁ := by rw [← Q.map_comp, c.hp₁]

variable {I : Type*} {T : D} {U : I → D} {g : ∀ i, U i ⟶ T}
  (sq : ∀ i j, ChosenPullback (g i) (g j))
  (sq₃ : ∀ i j k, ChosenPullback₃ (sq i j) (sq j k) (sq i k))
  (h : ∀ i j, IsPullback (Q.map (sq i j).p₁) (Q.map (sq i j).p₂)
    (Q.map (g i)) (Q.map (g j)))
  (h₃ : ∀ i j k, IsPullback (Q.map (sq₃ i j k).p₁₂) (Q.map (sq₃ i j k).p₂₃)
    (Q.map (sq i j).p₂) (Q.map (sq j k).p₁))

/-- The image under a functor of a chosen wide fibre product of three morphisms. -/
@[reducible] noncomputable def mapChosenPullback₃ (i j k : I) :
    ChosenPullback₃ (mapChosenPullback Q (sq i j) (h i j))
      (mapChosenPullback Q (sq j k) (h j k))
      (mapChosenPullback Q (sq i k) (h i k)) where
  chosenPullback := mapChosenPullback Q (sq₃ i j k).chosenPullback (h₃ i j k)
  p := Q.map (sq₃ i j k).p
  p₁ := Q.map (sq₃ i j k).p₁
  p₃ := Q.map (sq₃ i j k).p₃
  hp₁ := by dsimp [mapChosenPullback]; rw [← Q.map_comp, (sq₃ i j k).hp₁]
  hp₃ := by dsimp [mapChosenPullback]; rw [← Q.map_comp, (sq₃ i j k).hp₃]
  l := {
    f := Q.map (sq₃ i j k).p₁₃
    f_p₁ := by dsimp [mapChosenPullback]; rw [← Q.map_comp, (sq₃ i j k).p₁₃_p₁]
    f_p₂ := by dsimp [mapChosenPullback]; rw [← Q.map_comp, (sq₃ i j k).p₁₃_p₃]
    f_p := by dsimp [mapChosenPullback]; rw [← Q.map_comp, (sq₃ i j k).p₁₃_p] }

private theorem mapChosenPullback₃_p (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p = Q.map (sq₃ i j k).p := rfl

private theorem mapChosenPullback₃_p₁ (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p₁ = Q.map (sq₃ i j k).p₁ := rfl

private theorem mapChosenPullback₃_p₂ (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p₂ = Q.map (sq₃ i j k).p₂ := rfl

private theorem mapChosenPullback₃_p₃ (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p₃ = Q.map (sq₃ i j k).p₃ := rfl

private theorem mapChosenPullback₃_p₁₂ (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p₁₂ = Q.map (sq₃ i j k).p₁₂ := rfl

private theorem mapChosenPullback₃_p₂₃ (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p₂₃ = Q.map (sq₃ i j k).p₂₃ := rfl

private theorem mapChosenPullback₃_p₁₃ (i j k : I) :
    (mapChosenPullback₃ Q sq sq₃ h h₃ i j k).p₁₃ = Q.map (sq₃ i j k).p₁₃ := rfl

variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
  (L : ∀ i, F.obj (.mk (.op (Q.obj (U i)))))
  (hom : ∀ {V : D} (q : V ⟶ T) {i j : I} (a : V ⟶ U i) (b : V ⟶ U j),
    a ≫ g i = q → b ≫ g j = q →
    ((F.map (Q.map a).op.toLoc).toFunctor.obj (L i) ⟶
      (F.map (Q.map b).op.toLoc).toFunctor.obj (L j)))
  (hself : ∀ {V : D} (q : V ⟶ T) {i : I} (a : V ⟶ U i) (ha : a ≫ g i = q),
    hom q a a ha ha = 𝟙 _)
  (hcomp : ∀ {V : D} (q : V ⟶ T) {i j k : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (c : V ⟶ U k)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q) (hc : c ≫ g k = q),
    hom q a b ha hb ≫ hom q b c hb hc = hom q a c ha hc)
  (hpull : ∀ {V W : D} (r : W ⟶ V) (q : V ⟶ T) {i j : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (ha : a ≫ g i = q) (hb : b ≫ g j = q),
    pullHom (hom q a b ha hb) (Q.map r) (Q.map (r ≫ a)) (Q.map (r ≫ b))
      (by rw [Q.map_comp]) (by rw [Q.map_comp]) =
      hom (r ≫ q) (r ≫ a) (r ≫ b) (by rw [Category.assoc, ha])
        (by rw [Category.assoc, hb]))

include hpull in
/-- Compatibility of the comparisons with further restriction, with the composites named by
equations. -/
theorem diagramHom_pull {V W : D} (r : W ⟶ V)
    (q : V ⟶ T) (q' : W ⟶ T) {i j : I}
    (a : V ⟶ U i) (b : V ⟶ U j) (a' : W ⟶ U i) (b' : W ⟶ U j)
    (ha : a ≫ g i = q) (hb : b ≫ g j = q)
    (hq : r ≫ q = q') (har : r ≫ a = a') (hbr : r ≫ b = b') :
    pullHom (hom q a b ha hb) (Q.map r) (Q.map a') (Q.map b')
      (by rw [← Q.map_comp, har]) (by rw [← Q.map_comp, hbr]) =
      hom q' a' b' (by rw [← har, Category.assoc, ha, hq])
        (by rw [← hbr, Category.assoc, hb, hq]) := by
  subst hq har hbr
  exact hpull r q a b ha hb

/-- **A descent datum from a compatible family of comparisons.** Objects over the members of a
family of a category `D`, together with comparisons of their pullbacks over every object mapping
to two members, which are the identity on the diagonal, compose, and are compatible with further
restriction, form a descent datum for the image family in `C`. -/
noncomputable def diagramDescentData :
    F.DescentData' (fun i j => mapChosenPullback Q (sq i j) (h i j))
      (mapChosenPullback₃ Q sq sq₃ h h₃) where
  obj := L
  hom i j := hom (sq i j).p (sq i j).p₁ (sq i j).p₂ (sq i j).hp₁ (sq i j).hp₂
  pullHom'_hom_self i := by
    let c := sq i i
    let r := c.isPullback.lift (𝟙 _) (𝟙 _) (by simp)
    have hr₁ : r ≫ c.p₁ = 𝟙 _ := c.isPullback.lift_fst _ _ _
    have hr₂ : r ≫ c.p₂ = 𝟙 _ := c.isPullback.lift_snd _ _ _
    rw [Pseudofunctor.DescentData'.pullHom'_eq_pullHom _ _ _ _ (Q.map r)
      (hp₁ := by change Q.map r ≫ Q.map c.p₁ = _; rw [← Q.map_comp, hr₁, Q.map_id])
      (hp₂ := by change Q.map r ≫ Q.map c.p₂ = _; rw [← Q.map_comp, hr₂, Q.map_id])]
    have hr : r ≫ c.p = g i := by rw [← c.hp₁, ← Category.assoc, hr₁, Category.id_comp]
    have hh :=
      (diagramHom_pull Q L hom hpull r c.p (g i) c.p₁ c.p₂ (𝟙 _) (𝟙 _)
        c.hp₁ c.hp₂ hr hr₁ hr₂).trans (hself (g i) (𝟙 _) (by simp))
    have aux (a : Q.obj (U i) ⟶ Q.obj (U i)) (he : a = Q.map (𝟙 (U i)))
        (h₁ : Q.map r ≫ Q.map c.p₁ = a) (h₂ : Q.map r ≫ Q.map c.p₂ = a) :
        pullHom (hom c.p c.p₁ c.p₂ c.hp₁ c.hp₂) (Q.map r) a a h₁ h₂ = 𝟙 _ := by
      subst a
      exact hh
    exact aux _ (Q.map_id _).symm _ _
  pullHom'_hom_comp i j k := by
    rw [Pseudofunctor.DescentData'.pullHom'₁₂_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₂₃_eq_pullHom_of_chosenPullback₃,
      Pseudofunctor.DescentData'.pullHom'₁₃_eq_pullHom_of_chosenPullback₃]
    dsimp only [mapChosenPullback₃_p, mapChosenPullback₃_p₁, mapChosenPullback₃_p₂,
      mapChosenPullback₃_p₃, mapChosenPullback₃_p₁₂, mapChosenPullback₃_p₂₃,
      mapChosenPullback₃_p₁₃]
    rw [diagramHom_pull Q L hom hpull _ _ (sq₃ i j k).p _ _
      (sq₃ i j k).p₁ (sq₃ i j k).p₂ (sq i j).hp₁ (sq i j).hp₂
      (sq₃ i j k).p₁₂_p (sq₃ i j k).p₁₂_p₁ (sq₃ i j k).p₁₂_p₂,
      diagramHom_pull Q L hom hpull _ _ (sq₃ i j k).p _ _
      (sq₃ i j k).p₂ (sq₃ i j k).p₃ (sq j k).hp₁ (sq j k).hp₂
      (sq₃ i j k).p₂₃_p (sq₃ i j k).p₂₃_p₂ (sq₃ i j k).p₂₃_p₃,
      diagramHom_pull Q L hom hpull _ _ (sq₃ i j k).p _ _
      (sq₃ i j k).p₁ (sq₃ i j k).p₃ (sq i k).hp₁ (sq i k).hp₂
      (sq₃ i j k).p₁₃_p (sq₃ i j k).p₁₃_p₁ (sq₃ i j k).p₁₃_p₃]
    exact hcomp _ _ _ _ _ _ _

end

/-! ### Effectivity of fpqc descent, read on representatives -/

/-- Invertibility depends only on the isomorphism class of a sheaf of modules. -/
theorem isInvertible_of_iso {Z : Scheme.{u}} {M N : Z.Modules} (e : M ≅ N)
    (hM : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 M) :
    Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 N := by
  refine stacksIsInvertible_of_isFiniteLocallyFreeOfRank_one N ?_
  exact (Scheme.Modules.isFiniteLocallyFreeOfRank_iff N 1).mp
    (Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso e
      ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff M 1).mpr
        (isFiniteLocallyFreeOfRank_one_of_stacksIsInvertible M hM)))

/-- Reading off one component of a quasi-coherent descent datum, as a functor. -/
private def descentComponentFunctor {Z : Scheme.{u}} {ι : Type*} {Y : ι → Scheme.{u}}
    (u : ∀ i, Y i ⟶ Z) (i : ι) : QuasicoherentDescentData u ⥤ (Y i).Modules where
  obj D := D.component i
  map φ := φ.hom.hom i

/-- **A quasi-coherent descent datum for an fpqc covering comes from a quasi-coherent module on
the base**, whose pullbacks are isomorphic to the components of the datum. -/
theorem exists_isQuasicoherent_nonempty_iso_component {Z : Scheme.{u}}
    (𝒰 : PreZeroHypercover.{u + 1} Z)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} Z) (D : QuasicoherentDescentData 𝒰.f) :
    ∃ M : Z.Modules, M.IsQuasicoherent ∧
      ∀ i, Nonempty ((Scheme.Modules.pullback (𝒰.f i)).obj M ≅ D.component i) := by
  obtain ⟨M, ⟨e⟩⟩ := QuasicoherentDescentData.isEffective_fpqcPrecoverage 𝒰 h𝒰 D
  exact ⟨M.obj, M.property, fun i => ⟨(descentComponentFunctor 𝒰.f i).mapIso e⟩⟩

/-! ### Descent of invertibility along an fpqc covering -/

/-- The pullback of a free sheaf of modules along a morphism of schemes is free on the same
index type. -/
private def pullbackFreeIso {V Y : Scheme.{u}} (g : V ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback g).obj (SheafOfModules.free.{u} I) ≅ SheafOfModules.free.{u} I :=
  haveI : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs ((Scheme.Modules.pushforward g).IsRightAdjoint)
  haveI : (Opens.map g.base).Final := CategoryTheory.final_of_representablyFlat _
  (SheafOfModules.pullbackObjFreeIso.{u} g.toRingCatSheafHom I :
    (SheafOfModules.pullback g.toRingCatSheafHom).obj (SheafOfModules.free.{u} I) ≅
      SheafOfModules.free.{u} I)

/-- A free presentation of a sheaf of modules over an open `U` of the target pulls back to a
free presentation, on the same index type, of the pullback module over the preimage of `U`. -/
private def restrictPullbackFreeIso {V Y : Scheme.{u}} (g : V ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (I : Type u)
    (e : M.restrict U.ι ≅ SheafOfModules.free.{u} I) :
    ((Scheme.Modules.pullback g).obj M).restrict (g ⁻¹ᵁ U).ι ≅ SheafOfModules.free.{u} I :=
  (Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ U).ι).app _ ≪≫
    (Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι g U).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (g ∣_ U) U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e) ≪≫
    pullbackFreeIso (g ∣_ U) I

/-- An isomorphism of the restriction of a sheaf of modules to an open with the free sheaf on
`I` gives generating sections over that open, indexed by `I`, with invertible evaluation. -/
private theorem exists_generatingSections_of_restrict_iso {X : Scheme.{u}} (M : X.Modules)
    (V : X.Opens) (I : Type u) (e : M.restrict V.ι ≅ SheafOfModules.free.{u} I) :
    ∃ σ : (M.over V).GeneratingSections, IsIso σ.π ∧ Nonempty (σ.I ≃ I) := by
  let F := Scheme.Modules.overEquiv (X := X) V
  have hdisc : PreservesColimitsOfShape (Discrete I) F.functor :=
    preservesColimitsOfShape_of_discrete F.functor
  have hunit : SheafOfModules.unit (V.toScheme).ringCatSheaf ≅
      F.functor.obj (SheafOfModules.unit (X.ringCatSheaf.over V)) := Iso.refl _
  let eFree := @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F.functor I hdisc hunit
  let e' : F.functor.obj (M.over V) ≅ F.functor.obj (SheafOfModules.free.{u} I) :=
    (Scheme.Modules.overFunctorEquiv (X := X) V).app M ≪≫ e ≪≫ eFree
  let e'' : M.over V ≅ SheafOfModules.free.{u} I := F.fullyFaithfulFunctor.preimageIso e'
  refine ⟨(SheafOfModules.free.generatingSections I).ofEpi e''.inv, ?_, ⟨Equiv.refl I⟩⟩
  have h₀ : IsIso (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over V) I).π := by
    rw [SheafOfModules.free.generatingSections_π]
    exact IsIso.id _
  rw [SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₀ inferInstance

/-- The rank of a finite locally free sheaf of modules at a point of an open over which it is
free on an index type `I` is the cardinality of `I`. -/
private theorem finiteLocallyFreeRank_eq_card' {X : Scheme.{u}} (M : X.Modules)
    [hM : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := LocallyFreeRank.toRingSheaf X.toTopCat X.sheaf) M]
    (U : X.Opens) (I : Type u) (e : M.restrict U.ι ≅ SheafOfModules.free.{u} I)
    (x : X) (hx : x ∈ U) :
    Stacks.SheafOfModules.finiteLocallyFreeRank M
      (LocallyFreeRank.scheme_stalksNontrivial X) x = Nat.card I := by
  obtain ⟨q₀, hq₀, -⟩ := hM.exists_isFiniteLocallyFreeData
  obtain ⟨σ, hσ, ⟨eσ⟩⟩ := exists_generatingSections_of_restrict_iso M U I e
  let q : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := Option q₀.I
      X := fun i => match i with
        | none => U
        | some j => q₀.X j
      coversTop := by
        refine (Opens.coversTop_iff _ _).2 (eq_top_iff.mpr fun y _ => ?_)
        have h : (⨆ j, q₀.X j) = ⊤ := (Opens.coversTop_iff _ q₀.X).1 q₀.coversTop
        have hy : y ∈ (⨆ j, q₀.X j) := h ▸ trivial
        rw [TopologicalSpace.Opens.mem_iSup] at hy
        obtain ⟨j, hj⟩ := hy
        rw [TopologicalSpace.Opens.mem_iSup]
        exact ⟨some j, hj⟩
      generators := fun i => match i with
        | none => σ
        | some j => q₀.generators j }
  have hq : q.IsLocallyFreeData := ⟨fun | none => hσ | some j => hq₀.isIso j⟩
  rw [Stacks.SheafOfModules.finiteLocallyFreeRank_eq_card M
    (LocallyFreeRank.scheme_stalksNontrivial X) q hq none x hx]
  exact Nat.card_congr eσ

/-- **Invertibility descends along an fpqc covering.** A quasi-coherent module on a scheme whose
pullback to every member of an fpqc covering is invertible is itself invertible. -/
theorem isInvertible_of_pullback_fpqcCover {Y : Scheme.{u}} (M : Y.Modules)
    (hM : M.IsQuasicoherent) (𝒰 : Y.Cover.{v} Scheme.fpqcPrecoverage)
    (h : ∀ i, Stacks.SheafOfModules.IsInvertible (𝒰.X i).presheaf (𝒰.X i).ringCatSheaf.2
      ((Scheme.Modules.pullback (𝒰.f i)).obj M)) :
    Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 M := by
  have : M.IsQuasicoherent := hM
  have hrank : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) 1 := fun i =>
    isFiniteLocallyFreeOfRank_one_of_stacksIsInvertible _ (h i)
  have hflfi : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) := fun i =>
    have := hrank i
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) 1
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
    AlgebraicGeometry.isFiniteLocallyFree_of_pullback_fpqcCover M 𝒰 hflfi
  refine stacksIsInvertible_of_isFiniteLocallyFreeOfRank_one M
    ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff M 1).1 ?_)
  intro y
  obtain ⟨U, hyU, I, hIfin, ⟨e⟩⟩ := (Scheme.Modules.isFiniteLocallyFree_iff M).2 hflf y
  have := Scheme.instJointlySurjectivePrecoverage (P := @Flat)
  obtain ⟨i, z, hz⟩ := 𝒰.forgetQc.exists_eq y
  have := hrank i
  have hflf' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) := hflfi i
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := LocallyFreeRank.toRingSheaf (𝒰.X i).toTopCat (𝒰.X i).sheaf)
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) := hflf'
  have hzU : z ∈ (𝒰.f i) ⁻¹ᵁ U := by
    show (𝒰.f i).base z ∈ U
    rw [hz]
    exact hyU
  have h₁ := finiteLocallyFreeRank_eq_card' ((Scheme.Modules.pullback (𝒰.f i)).obj M)
    ((𝒰.f i) ⁻¹ᵁ U) I (restrictPullbackFreeIso (𝒰.f i) M U I e) z hzU
  obtain ⟨U', hzU', ⟨e'⟩⟩ :=
    (Scheme.Modules.isFiniteLocallyFreeOfRank_iff
      ((Scheme.Modules.pullback (𝒰.f i)).obj M) 1).2 (hrank i) z
  have h₂ := finiteLocallyFreeRank_eq_card' ((Scheme.Modules.pullback (𝒰.f i)).obj M)
    U' (ULift.{u, 0} (Fin 1)) e' z hzU'
  have : Finite I := hIfin
  have hcard : Nat.card I = 1 := by
    rw [h₁.symm.trans h₂, Nat.card_congr Equiv.ulift, Nat.card_fin]
  exact ⟨U, hyU, ⟨e ≪≫ (SheafOfModules.freeFunctor.mapIso
    ((Finite.equivFinOfCardEq hcard).trans Equiv.ulift.symm).toIso :
      SheafOfModules.free.{u} I ≅ SheafOfModules.free.{u} (ULift.{u, 0} (Fin 1)))⟩⟩

end Stacks.Picard

end
