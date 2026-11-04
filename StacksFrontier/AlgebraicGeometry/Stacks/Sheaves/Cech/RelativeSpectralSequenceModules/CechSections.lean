module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.Algebra.Homology.DerivedCategory.FunctorialInjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsTo
public import StacksFrontier.Algebra.Homology.SpectralSequence.DerivedTensor
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Functoriality
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.TwoFibreProductEqualizers
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Comp
import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Subobject.CokernelComparisons
public import StacksFrontier.Homology.DerivedIndexing.Extend
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequenceModules.ModuleRestriction

/-!
# The sections double complex of the relative Čech nerve

Every term of the relative Čech nerve of a faithful functor whose source has equalizers has
equalizers. This file defines the first-page terms `tupleModuleCohomology` and the data
`ModuleSpectralSequenceData` of the relative Čech-to-cohomology spectral sequence for sheaves of
modules, and builds the double complex of sections on the relative Čech nerve of an injective
resolution, whose columns compute the cohomology of the inverse images.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ZeroObject

namespace Stacks.RelativeCech

universe u vᵤ vₓ wᵤ wₓ a v₁ w₁ v₂ w₂ r

section CechLimits

universe vC vU vX uC uU uX

variable {C : Type uC} [Category.{vC} C] {U : Type uU} [Category.{vU} U]
  {X : Type uX} [Category.{vX} X] (q : X ⥤ C) (f : U ⥤ X)
/-- If a fully faithful, essentially surjective functor lands in a category with equalizers, its
source has equalizers. -/
private lemma hasEqualizers_of_fullyFaithful_essSurj {A B : Type*} [Category A] [Category B]
    {F : A ⥤ B} (e : F.FullyFaithful) [F.EssSurj] [HasEqualizers B] : HasEqualizers A := by
  let := e.full
  let := e.faithful
  let : F.IsEquivalence := {}
  exact Adjunction.hasLimitsOfShape_of_equivalence F

/-- A tuple of degree zero has a single source object; this is the resulting functor to `𝒰`. -/
private def cechZeroSource : Tuple q f 0 ⥤ U where
  obj a := a.source 0
  map g := g.source 0
/-- A morphism between the source objects of two degree-zero tuples, as a family indexed by
`Fin 1`. -/
private def cechZeroHomSource {a b : Tuple q f 0} (g : a.source 0 ⟶ b.source 0) :
    ∀ i, a.source i ⟶ b.source i :=
  Fin.cases g (fun j => j.elim0)

/-- A morphism of degree-zero tuples is determined by, and can be built from, its source component,
so `cechZeroSource` is fully faithful. -/
private def cechZeroSourceFullyFaithful : (cechZeroSource q f).FullyFaithful where
  preimage {a b} g :=
    { target := (a.comparison 0).inv ≫ f.map g ≫ (b.comparison 0).hom
      source := cechZeroHomSource q f g
      comparison_naturality i := by
        have hi : i = 0 := by omega
        subst hi
        change f.map g ≫ _ = _
        simp
        rfl }
  map_preimage := by intros; rfl
  preimage_map {a b} g := by
    apply tuple_hom_ext
    · dsimp [cechZeroSource]
      rw [g.comparison_naturality]
      simp
    · funext i
      have hi : i = 0 := by omega
      subst hi
      rfl
/-- The degree-zero tuple attached to an object of `𝒰`, with identity comparison isomorphism. -/
private def cechZeroDiagonal (a : U) : Tuple q f 0 where
  target := f.obj a
  source := fun _ => a
  comparison := fun _ => Iso.refl _
  comparison_lift := fun _ => IsHomLift.id rfl
/-- `cechZeroSource` is essentially surjective, `cechZeroDiagonal` providing the preimages. -/
private lemma cechZeroSourceEssSurj : (cechZeroSource q f).EssSurj where
  mem_essImage a := ⟨cechZeroDiagonal q f a, ⟨Iso.refl _⟩⟩
/-- If `𝒰` has equalizers, so does the degree-zero term of the relative Čech nerve of `f`. -/
private lemma cechZero_hasEqualizers [HasEqualizers U] :
    HasEqualizers (Tuple q f 0) := by
  let := cechZeroSourceEssSurj q f
  exact hasEqualizers_of_fullyFaithful_essSurj (cechZeroSourceFullyFaithful q f)

/-- The two-fold fibre product over `𝒳` of `𝒰` with the degree-`n` term of the relative Čech
nerve. -/
private abbrev cechProduct (n : ℕ) :=
  TwoFibreProductOver (f ⋙ q) (Tuple.projection q f n ⋙ q) q
    f (Tuple.projection q f n)
/-- The degree-`n + 1` term of the relative Čech nerve as the two-fold fibre product of `𝒰` with
its degree-`n` term. -/
@[implicit_reducible] private def cechToProduct (n : ℕ) :
    Tuple q f (n + 1) ⥤ cechProduct q f n where
  obj a :=
    { base := q.obj a.target
      x := a.source 0
      y := (Tuple.reindex q f Fin.succ).obj a
      hx := by
        have := a.comparison_lift 0
        exact IsHomLift.domain_eq q (𝟙 (q.obj a.target)) (a.comparison 0).hom
      hy := rfl
      iso := a.comparison 0
      vertical := a.comparison_lift 0 }
  map {a b} g :=
    { hbase := q.map g.target
      a := g.source 0
      b := (Tuple.reindex q f Fin.succ).map g
      ha := by
        have ha := a.comparison_lift 0
        have hb := b.comparison_lift 0
        refine IsHomLift.of_commsq (f ⋙ q) _ _
          (IsHomLift.domain_eq q (𝟙 (q.obj a.target)) (a.comparison 0).hom)
          (IsHomLift.domain_eq q (𝟙 (q.obj b.target)) (b.comparison 0).hom) ?_
        have e := congrArg (fun k => q.map k) (g.comparison_naturality 0)
        simp only [Functor.map_comp] at e
        rw [IsHomLift.fac' q (𝟙 (q.obj a.target)) (a.comparison 0).hom,
          IsHomLift.fac' q (𝟙 (q.obj b.target)) (b.comparison 0).hom] at e
        simpa only [Functor.comp_obj, Functor.comp_map, eqToHom_refl, Category.id_comp,
            Category.comp_id] using e
      hb := IsHomLift.of_fac' _ _ _ rfl rfl (by simp [Tuple.projection, Tuple.reindex])
      w := g.comparison_naturality 0 }
  map_id a := TwoFibreProductOver.Hom.ext' rfl rfl
  map_comp g h := TwoFibreProductOver.Hom.ext' rfl rfl
/-- The tuple attached to an object of the two-fold fibre product, obtained by adjoining the extra
source object in degree zero. -/
@[implicit_reducible] private def cechFromProductObj {n : ℕ} (a : cechProduct q f n) :
    Tuple q f (n + 1) where
  target := a.y.target
  source := Fin.cases a.x a.y.source
  comparison := Fin.cases a.iso a.y.comparison
  comparison_lift i := by
    refine Fin.cases ?_ (fun j => a.y.comparison_lift j) i
    dsimp
    have h := a.vertical
    change q.IsHomLift (𝟙 (q.obj a.y.target)) a.iso.hom
    rw [show q.obj a.y.target = a.base from a.hy]
    exact h
/-- `cechToProduct` is fully faithful. -/
private def cechToProductFullyFaithful (n : ℕ) : (cechToProduct q f n).FullyFaithful where
  preimage {a b} g :=
    { target := g.b.target
      source := fun i => Fin.cases g.a g.b.source i
      comparison_naturality := fun i => Fin.cases g.w g.b.comparison_naturality i }
  map_preimage g := by
    apply TwoFibreProductOver.Hom.ext'
    · rfl
    · exact tuple_hom_ext _ _ rfl (funext fun _ => rfl)
  preimage_map g := by
    refine tuple_hom_ext _ _ rfl ?_
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
/-- `cechToProduct` is essentially surjective, `cechFromProductObj` providing the preimages. -/
private lemma cechToProductEssSurj (n : ℕ) : (cechToProduct q f n).EssSurj where
  mem_essImage a := by
    refine ⟨cechFromProductObj q f a, ⟨eqToIso ?_⟩⟩
    cases a with
    | mk base x y hx hy iso vertical =>
      dsimp at hy
      cases hy
      rfl
/-- If the presenting two-fold fibre product has equalizers, so does the degree-`n + 1` term of the
relative Čech nerve of `f`. -/
private lemma cechSucc_hasEqualizers (n : ℕ) [HasEqualizers (cechProduct q f n)] :
    HasEqualizers (Tuple q f (n + 1)) := by
  let := cechToProductEssSurj q f n
  exact hasEqualizers_of_fullyFaithful_essSurj (cechToProductFullyFaithful q f n)
/-- For `f` faithful and `𝒰` with equalizers, every term of the relative Čech nerve of `f` has
equalizers. -/
private lemma cech_hasEqualizers
    (hq : q.IsFiberedInGroupoids) (hf : (f ⋙ q).IsFiberedInGroupoids)
    (h : ∀ n, (Tuple.projection q f n ⋙ q).IsFiberedInGroupoids)
    [f.Faithful] [HasEqualizers U] (n : ℕ) : HasEqualizers (Tuple q f n) := by
  induction n with
  | zero => exact cechZero_hasEqualizers q f
  | succ n ih =>
    let := ih
    let := tuple_projection_faithful q f n
    let := CategoryTheory.TwoFibreProductOver.hasEqualizers (f ⋙ q)
      (Tuple.projection q f n ⋙ q) q f (Tuple.projection q f n)
      hf (h n) hq rfl rfl
    exact cechSucc_hasEqualizers q f n

end CechLimits

/-- Restriction of global sections of a presheaf of rings along a functor: a compatible
family of sections indexed by `D` restricts to one indexed by `C`. -/
public def globalSectionsRestrict {C : Type v₁} [Category.{w₁} C] {D : Type v₂}
    [Category.{w₂} D] (π : C ⥤ D) (F : Dᵒᵖ ⥤ RingCat.{r}) :
    RingCat.sectionsSubring F →+* RingCat.sectionsSubring (π.op ⋙ F) where
  toFun s := ⟨fun y => s.1 (π.op.obj y), fun {_ _} g => s.2 (π.op.map g)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 : Type vᵤ} [Category.{wᵤ} 𝒰] {𝒳 : Type vₓ} [Category.{wₓ} 𝒳]
  (p : 𝒰 ⥤ AlgebraicGeometry.BigFppfOver B S hS) (q : 𝒳 ⥤ AlgebraicGeometry.BigFppfOver B S hS)
  (f : 𝒰 ⥤ 𝒳) (τ : AlgebraicGeometry.SiteKind)

universe t

/-- Abelian sheaves on a site on `𝒳` admit sheafification in any universe in which `𝒳` is
essentially small. -/
private theorem siteHasSheafifyAt (J : GrothendieckTopology 𝒳) [EssentiallySmall.{t} 𝒳] :
    HasSheafify J AddCommGrpCat.{t} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{t, _, _} J

/-- Sheafification of abelian sheaves on a site on `𝒳` inverts exactly the locally bijective
maps, in any universe in which `𝒳` is essentially small. -/
private theorem siteWEqualsLocallyBijectiveAt (J : GrothendieckTopology 𝒳)
    [EssentiallySmall.{t} 𝒳] : J.WEqualsLocallyBijective AddCommGrpCat.{t} :=
  have : ((equivSmallModel.{t} 𝒳).inverse.inducedTopology J).WEqualsLocallyBijective
      AddCommGrpCat.{t} :=
    inferInstance
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{_, _, _, _, t}
    (A := AddCommGrpCat.{t}) J

attribute [local instance] siteHasSheafifyAt siteWEqualsLocallyBijectiveAt

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

/-- The structure functor of the degree-`n` term `𝒰_n` of the relative Čech nerve of `f`:
its projection `f_n` to `𝒳` followed by the structure functor of `𝒳`. -/
public abbrev tupleStructureFunctor (n : ℕ) :
    Tuple q f n ⥤ AlgebraicGeometry.BigFppfOver B S hS :=
  Tuple.projection q f n ⋙ q

/-- `Hʲ((𝒰ᵢ)_τ, fᵢ^*𝓕)`, the degree-`j` module cohomology of the inverse image of `𝓕`
on the degree-`i` term of the relative Čech nerve, with its scalars restricted from
`Γ(𝒪_{𝒰ᵢ})` to `Γ(𝒪_𝒳)`. -/
public def tupleModuleCohomology (hq : q.IsFiberedInGroupoids) (i j : ℕ)
    (hi : (tupleStructureFunctor B S hS q f i).IsFiberedInGroupoids)
    (𝓕 : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) :
    ModuleCat.{max u vᵤ vₓ wᵤ wₓ a}
      (Stacks.Cohomology.SiteModules.GlobalSectionRing
          (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) :=
  (ModuleCat.restrictScalars (globalSectionsRestrict (Tuple.projection q f i)
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj)).obj
    ((Stacks.Cohomology.SiteModules.globalModuleCohomology.{max vᵤ vₓ wₓ, max wᵤ wₓ, u,
        max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS
          (tupleStructureFunctor B S hS q f i) hi (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) j).obj
      ((AlgebraicGeometry.Stack.modulePullback.{u, max vᵤ vₓ wₓ, max wᵤ wₓ, max u vᵤ vₓ wᵤ wₓ a,
          vₓ, wₓ}
        B S hS (tupleStructureFunctor B S hS q f i) q hi hq
        (Tuple.projection q f i) rfl (B.baseTopology τ) (B.baseTopology_le_topology τ)).obj 𝓕))

/-- The first page and the finite abutment of the relative Čech spectral sequence of a
sheaf of modules, as a spectral sequence of `Γ(𝒪_𝒳)`-modules. -/
public structure ModuleSpectralSequenceData (hq : q.IsFiberedInGroupoids)
    (𝓕 : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) where
  /-- Each term of the relative Čech nerve is fibred in groupoids over the base site. -/
  fiberedInGroupoids (n : ℕ) : (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids
  /-- A spectral sequence of `Γ(𝒪_𝒳)`-modules, starting at its first page. -/
  sequence : CohomologicalSpectralSequence
    (ModuleCat.{max u vᵤ vₓ wᵤ wₓ a}
      (Stacks.Cohomology.SiteModules.GlobalSectionRing
          (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)))) 1
  /-- The first page is the module cohomology of the inverse images on the terms of the
  relative Čech nerve. -/
  pageOneIso (i j : ℕ) :
    (sequence.page 1).X ((i : ℤ), (j : ℤ)) ≅
      tupleModuleCohomology.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq i j
        (fiberedInGroupoids i) 𝓕
  /-- All terms outside the first quadrant vanish. -/
  firstQuadrant (i j : ℤ) (h : (i < 0) ∨ (j < 0)) :
    IsZero ((sequence.page 1).X (i, j))
  /-- The finite filtration abuts to the module cohomology of `𝓕` on `𝒳_τ`. -/
  abutment : sequence.AbutsTo (fun n : ℤ =>
    if n < 0 then 0 else
      (Stacks.Cohomology.SiteModules.globalModuleCohomology.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
        (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) n.toNat).obj 𝓕)

section

/-- Global sections on the degree-`n` term of the relative Čech nerve of the inverse image of a
sheaf of modules, with scalars restricted to `Γ(𝒪_𝒳)`. -/
private abbrev cechLevelSectionsFunctor (hq : q.IsFiberedInGroupoids) (n : ℕ)
    (hn : (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :=
  AlgebraicGeometry.Stack.modulePullback.{u, max vᵤ vₓ wₓ, max wᵤ wₓ,
      max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ}
      B S hS (tupleStructureFunctor B S hS q f n) q hn hq
      (Tuple.projection q f n) rfl (B.baseTopology τ) (B.baseTopology_le_topology τ) ⋙
    Stacks.Cohomology.SiteModules.globalSectionsFunctor
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS
        (tupleStructureFunctor B S hS q f n) hn (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) ⋙
    ModuleCat.restrictScalars (globalSectionsRestrict (Tuple.projection q f n)
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj)

/-- `cechLevelSectionsFunctor` is additive. -/
private theorem cechLevelSectionsFunctor_additive (hq : q.IsFiberedInGroupoids) (n : ℕ)
    (hn : (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :
    (cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq n hn).Additive where
  map_add := by intros; rfl

attribute [local instance] cechLevelSectionsFunctor_additive

/-- The map of degree-`m` to degree-`n` sections induced by a map `Fin (m + 1) → Fin (n + 1)` of
index sets, by reindexing the tuples. -/
private def cechLevelSectionsMap (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    {m n : ℕ} (φ : Fin (m + 1) → Fin (n + 1)) :
    cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq m (h m) ⟶
      cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq n (h n) where
  app M := ModuleCat.ofHom
    (X := (cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq m (h m)).obj M)
    (Y := (cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq n (h n)).obj M)
    { toFun := fun s => ⟨fun x => s.val ((Tuple.reindex q f φ).op.obj x),
        fun g => s.property ((Tuple.reindex q f φ).op.map g)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality := by intros; rfl

/-- Reindexing along the identity induces the identity on sections. -/
private lemma cechLevelSectionsMap_id (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) (n : ℕ) :
    cechLevelSectionsMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h
      (id : Fin (n + 1) → Fin (n + 1)) = 𝟙 _ := by
  ext M s
  rfl

/-- Reindexing composes contravariantly on sections. -/
private lemma cechLevelSectionsMap_comp (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    {l m n : ℕ} (φ : Fin (l + 1) → Fin (m + 1)) (ψ : Fin (m + 1) → Fin (n + 1)) :
    cechLevelSectionsMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h (ψ ∘ φ) =
      cechLevelSectionsMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h φ ≫
        cechLevelSectionsMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h ψ := by
  ext M s
  rfl

/-- The cosimplicial object of sections functors of the relative Čech nerve of `f`. -/
@[implicit_reducible] private def cechSectionsCosimplicial (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :
    CosimplicialObject (SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
        (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) ⥤
      ModuleCat.{max u vᵤ vₓ wᵤ wₓ a}
        (Stacks.Cohomology.SiteModules.GlobalSectionRing
            (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)))) where
  obj n := cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq n.len (h n.len)
  map φ := cechLevelSectionsMap.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h φ.toOrderHom
  map_id n := cechLevelSectionsMap_id.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h n.len
  map_comp φ ψ := cechLevelSectionsMap_comp.{u, vᵤ, vₓ, wᵤ, wₓ, a}
    B S hS q f τ hq h φ.toOrderHom ψ.toOrderHom

/-- The relative Čech complex of sections of a sheaf of modules: the alternating coface complex of
`cechSectionsCosimplicial`. -/
private abbrev cechSectionsComplexFunctor (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :=
  (cechSectionsCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).flip ⋙
    AlgebraicTopology.alternatingCofaceMapComplex _

/-- The relative Čech complex of sections is additive in the sheaf of modules. -/
private theorem cechSectionsComplexFunctor_additive (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :
    (cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq h).Additive where
  map_add := by
    intro M N α β
    ext n s
    rfl

attribute [local instance] cechSectionsComplexFunctor_additive

/-- The augmentation of the sections complex: global sections on `𝒳` restrict to sections on the
degree-zero term of the relative Čech nerve. -/
private def cechSectionsAugmentation (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :
    Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) ⟶
      cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq 0 (h 0) where
  app M := ModuleCat.ofHom
    (X := (Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))).obj M)
    (Y := (cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq 0 (h 0)).obj M)
    { toFun := fun s => ⟨fun x => s.val ((Tuple.projection q f 0).op.obj x),
        fun g => s.property ((Tuple.projection q f 0).op.map g)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality := by intros; rfl

/-- The augmentation of the sections complex lands in the kernel of the first differential. -/
private lemma cechSectionsAugmentation_d (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    (M : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) :
    (cechSectionsAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).app M ≫
      ((cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).obj M).d 0 1 = 0 := by
  show (cechSectionsAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).app M ≫
    AlgebraicTopology.AlternatingCofaceMapComplex.objD
      ((cechSectionsCosimplicial.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).flip.obj M) 0 = 0
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Nat.reduceAdd, Fin.sum_univ_two,
    Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul,
    ← sub_eq_add_neg]
  rw [Preadditive.comp_sub, sub_eq_zero]
  ext s
  rfl

/-- The augmentation of global sections into the relative Čech complex of sections, as a map of
cochain complexes. -/
private def cechSectionsAugmentationComplex (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids) :
    Stacks.Cohomology.SiteModules.globalSectionsFunctor.{vₓ, wₓ, u, max u vᵤ vₓ wᵤ wₓ a}
        (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)) ⋙
        HomologicalComplex.single _ (ComplexShape.up ℕ) 0 ⟶
      cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h where
  app M := HomologicalComplex.mkHomFromSingle
    ((cechSectionsAugmentation.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).app M)
    (fun j hj => by
      have : j = 1 := hj.symm
      subst j
      exact cechSectionsAugmentation_d.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h M)
  naturality {M N} α := by
    apply HomologicalComplex.from_single_hom_ext
    ext s
    rfl

/-- The double complex obtained by applying the relative Čech complex of sections to a cochain
complex of sheaves of modules. -/
private abbrev cechModuleDoubleComplex (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    (K : CochainComplex (SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) ℕ) := by
  letI := cechSectionsComplexFunctor_additive.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h
  letI := cechSectionsComplexFunctor_additive.{u, vᵤ, vₓ, wᵤ, wₓ, a}
    B S hS q f τ hq h
  letI : (cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq h).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  exact HomologicalComplex₂.flip
      (((cechSectionsComplexFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj K)

/-- The degree-`n` column of the relative Čech double complex is the degree-`n` sections
complex. -/
private lemma cechModuleDoubleComplex_column (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    (K : CochainComplex (SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ))) ℕ) (n : ℕ) :
    (cechModuleDoubleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq h K).X n =
      ((cechLevelSectionsFunctor.{u, vᵤ, vₓ, wᵤ, wₓ, a} B S hS q f τ hq n
          (h n)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K := by
  rfl

/-- The degree-`j` cohomology of the degree-`i` column of the relative Čech double complex of an
injective resolution of `𝓕` is `Hʲ((𝒰ᵢ)_τ, fᵢ^*𝓕)`. -/
private def cechColumnCohomologyIso
    (hq : q.IsFiberedInGroupoids)
    (h : ∀ n, (tupleStructureFunctor B S hS q f n).IsFiberedInGroupoids)
    (heq : ∀ n, HasEqualizers (Tuple q f n)) [f.Faithful]
    (𝓕 : SheafOfModules.{max u vᵤ vₓ wᵤ wₓ a}
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)))
    (I : InjectiveResolution 𝓕) (i j : ℕ) :
    ((cechModuleDoubleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq h I.cocomplex).X i).homology j ≅
      tupleModuleCohomology.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq i j (h i) 𝓕 := by
  let := heq i
  let := tuple_projection_faithful q f i
  let L := AlgebraicGeometry.Stack.modulePullback.{u, max vᵤ vₓ wₓ, max wᵤ wₓ,
    max u vᵤ vₓ wᵤ wₓ a, vₓ, wₓ}
    B S hS (tupleStructureFunctor B S hS q f i) q (h i) hq
    (Tuple.projection q f i) rfl (B.baseTopology τ) (B.baseTopology_le_topology τ)
  letI : L.Additive := { map_add := by intros; rfl }
  have hL := moduleRestriction_exact.{u, max vᵤ vₓ wₓ, vₓ, max wᵤ wₓ, wₓ, a}
    B S hS q (Tuple.projection q f i) τ hq (h i)
  letI : PreservesFiniteLimits L := hL.1
  letI : PreservesFiniteColimits L := hL.2
  letI : L.PreservesInjectiveObjects := ⟨fun {M} hM => by
    let := hM
    exact moduleRestriction_preservesInjectives.{u, max vᵤ vₓ wₓ, vₓ,
      max wᵤ wₓ, wₓ, a} B S hS q (Tuple.projection q f i) τ hq (h i) M⟩
  let J := mapInjectiveResolutionOfPreservesInjectives L I
  let O := AlgebraicGeometry.Stack.ringStructureSheafCore B S hS
      (tupleStructureFunctor B S hS q f i) (h i) (B.baseTopology τ)
        (B.baseTopology_le_topology τ)
  let G := Stacks.Cohomology.SiteModules.globalSectionsFunctor.{max vᵤ vₓ wₓ, max wᵤ wₓ, u,
    max u vᵤ vₓ wᵤ wₓ a} O
  let φ : Stacks.Cohomology.SiteModules.GlobalSectionRing
        (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
          (B.baseTopology_le_topology τ)) →+*
      Stacks.Cohomology.SiteModules.GlobalSectionRing O :=
    globalSectionsRestrict (Tuple.projection q f i)
      (AlgebraicGeometry.Stack.ringStructureSheafCore B S hS q hq (B.baseTopology τ)
        (B.baseTopology_le_topology τ)).obj
  let R := ModuleCat.restrictScalars.{max u vᵤ vₓ wᵤ wₓ a} φ
  letI : R.PreservesHomology := restrictScalars_preservesHomology φ
  let C := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
  have hcol : (cechModuleDoubleComplex.{u, vᵤ, vₓ, wᵤ, wₓ, a}
        B S hS q f τ hq h I.cocomplex).X i =
      (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj C :=
    (cechModuleDoubleComplex_column.{u, vᵤ, vₓ, wᵤ, wₓ, a}
      B S hS q f τ hq h I.cocomplex i).trans rfl
  exact (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) j).mapIso (eqToIso hcol) ≪≫
    (C.sc j).mapHomologyIso R ≪≫
    R.mapIso (Stacks.Cohomology.SiteModules.globalModuleCohomologyIso.{max vᵤ vₓ wₓ,
      max wᵤ wₓ, u, max u vᵤ vₓ wᵤ wₓ a} O (L.obj 𝓕) J j).symm

end

end Stacks.RelativeCech

end
