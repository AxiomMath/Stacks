module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
public import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# Local sections of constant sheaves of modules

Let `(C, J)` be a site and `Λ` a commutative ring. This file collects the local statements about
constant sheaves of `Λ`-modules that the induction of Stacks Tag 094G runs on: that a constant
sheaf restricts to a constant sheaf on a slice site, that local constancy of finite type is
inherited by restrictions, that a locally constant sheaf of finite type is locally a quotient of
the constant sheaf on a finite free module, that a morphism of constant sheaves is locally
induced by a homomorphism of modules, and that sections and maps out of a constant finite free
sheaf lift along an epimorphism over a covering family.

## Main results

* `Stacks.ConstantSheaf.constantSheafOverIso`: a constant sheaf restricts to a constant sheaf.
* `Stacks.ConstantSheaf.finiteTypeLocallyConstant_over`: local constancy of finite type passes
  to a slice site.
* `Stacks.ConstantSheaf.exists_cover_constantFree_epi`: locally, a locally constant sheaf of
  finite type is the constant sheaf on a quotient of a finite free module.
* `Stacks.ConstantSheaf.exists_cover_fixed_constant_map`: a morphism of constant sheaves is
  locally the constant sheaf of a homomorphism of modules (Stacks Tag 093S).
* `Stacks.ConstantSheaf.exists_cover_lift_constantFree`: a map out of a constant finite free
  sheaf lifts along an epimorphism over a covering family.

## Implementation notes

The module universe is `max u v w` and `Λ` lives in `Type w`, which is the shape of
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf` and the smallest universe at which
a finite free `Λ`-module is an object of the module category; see
`Stacks.ConstantSheaf.freeMod`.

## References

* [Stacks Project, Tag 094G](https://stacks.math.columbia.edu/tag/094G)
* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace Stacks.ConstantSheaf

universe v u w m

attribute [local instance] HasDerivedCategory.standard

attribute [local implicit_reducible] constantSheaf Functor.sheafPushforwardContinuous
  HomologicalComplex.homologyFunctor HomologicalComplex.homology
  ShortComplex.LeftHomologyData.map

set_option linter.checkUnivs false in
/-- The free `Λ`-module of rank `n`, as an object of the module universe `max u v w`. -/
abbrev freeMod (Λ : Type w) [CommRing Λ] (n : ℕ) : ModuleCat.{max u v w} Λ :=
  ModuleCat.of Λ (ULift.{max u v} (Fin n →₀ Λ))

/-- `freeMod Λ n` is the free `Λ`-module on `Fin n`, up to the universe lift. -/
def freeModEquiv (Λ : Type w) [CommRing Λ] (n : ℕ) :
    (freeMod.{v, u, w} Λ n : Type (max u v w)) ≃ₗ[Λ] (Fin n →₀ Λ) :=
  ULift.moduleEquiv

/-- `freeMod Λ n` is a finitely generated `Λ`-module. -/
theorem isFG_freeMod (Λ : Type w) [CommRing Λ] (n : ℕ) :
    ModuleCat.isFG Λ (freeMod.{v, u, w} Λ n) := by
  rw [ModuleCat.isFG_iff]
  exact Module.Finite.equiv (freeModEquiv.{v, u, w} Λ n).symm

/-- Refining every member of a covering family by a covering family again gives a covering
family: the composites `V i j ⟶ U i ⟶ X` generate a covering sieve of `X`. -/
lemma covering_ofArrows_comp
    {C : Type*} [Category* C] (J : GrothendieckTopology C)
    {X : C} {I : Type*} (U : I → C) (f : ∀ i, U i ⟶ X)
    (hf : Sieve.ofArrows U f ∈ J X)
    {A : I → Type*} (V : ∀ i, A i → C) (g : ∀ i j, V i j ⟶ U i)
    (hg : ∀ i, Sieve.ofArrows (V i) (g i) ∈ J (U i)) :
    Sieve.ofArrows (fun p : Σ i, A i => V p.1 p.2)
      (fun p => g p.1 p.2 ≫ f p.1) ∈ J X := by
  apply J.transitive hf
  intro Y k hk
  rcases hk with ⟨Z, l, _, ⟨i⟩, rfl⟩
  apply J.superset_covering _ (J.pullback_stable l (hg i))
  intro W t ht
  rcases ht with ⟨Z', s, _, ⟨j⟩, hs⟩
  change Sieve.ofArrows _ _ (t ≫ l ≫ f i)
  rw [← Category.assoc, ← hs, Category.assoc]
  exact (Sieve.ofArrows _ _).downward_closed (Sieve.ofArrows_mk
    (fun p : Σ i, A i => V p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1) ⟨i, j⟩) s

/-- **The constant sheaf on a slice site is a restriction.** The component at `M` of the
compatibility of sheafification with pushforward along `Over.forget U`, which identifies
`constantSheaf (J.over U) M` with the restriction to `C/U` of `constantSheaf J M`. -/
noncomputable def constantSheafOverIso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) :
    (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).obj M ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) U).obj
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M) :=
  ((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{max u v w} Λ) (J.over U) J).app ((Functor.const Cᵒᵖ).obj M)

/-- `Stacks.ConstantSheaf.constantSheafOverIso` is natural in the module. -/
lemma constantSheafOverIso_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {A B : ModuleCat.{max u v w} Λ} (g : A ⟶ B) :
    (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).map g ≫
        (constantSheafOverIso J U B).hom =
      (constantSheafOverIso J U A).hom ≫
        (J.overPullback (ModuleCat.{max u v w} Λ) U).map
          ((constantSheaf J (ModuleCat.{max u v w} Λ)).map g) :=
  ((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{max u v w} Λ) (J.over U) J).hom.naturality
      ((Functor.const Cᵒᵖ).map g)

/-- Naturality of the unit of sheafification on constant presheaves, read on sections over an
object of the site. -/
lemma constantSheaf_unit_naturality
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    {A B : ModuleCat.{max u v w} Λ} (g : A ⟶ B) (U : C) :
    g ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op U) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) ≫
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).map g).hom.app (op U) :=
  congrArg (fun z => z.app (op U))
    (toSheafify_naturality J ((Functor.const Cᵒᵖ).map g))

/-- Restriction of sheaves of modules to a slice site preserves finite limits: it is restriction
of presheaves, which is computed pointwise, and the forgetful functor to presheaves reflects
and preserves finite limits. -/
lemma overPullback_preservesFiniteLimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] (U : C) :
    PreservesFiniteLimits (J.overPullback (ModuleCat.{max u v w} Λ) U) := by
  have : PreservesFiniteLimits
      (J.overPullback (ModuleCat.{max u v w} Λ) U ⋙
        sheafToPresheaf (J.over U) (ModuleCat.{max u v w} Λ)) := by
    change PreservesFiniteLimits
      (sheafToPresheaf J (ModuleCat.{max u v w} Λ) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.forget U).op)
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (sheafToPresheaf (J.over U) (ModuleCat.{max u v w} Λ))

/-- Restriction of sheaves of modules to a slice site preserves finite colimits, being a left
adjoint. -/
lemma overPullback_preservesFiniteColimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] (U : C) :
    PreservesFiniteColimits (J.overPullback (ModuleCat.{max u v w} Λ) U) := by
  have : PreservesColimitsOfSize.{0, 0} (J.overPullback (ModuleCat.{max u v w} Λ) U) :=
    ((Over.forget U).sheafAdjunctionCocontinuous (ModuleCat.{max u v w} Λ)
      (J.over U) J).leftAdjoint_preservesColimits
  infer_instance

attribute [local instance] overPullback_preservesFiniteLimits
  overPullback_preservesFiniteColimits

/-- For a continuous and cocontinuous functor `G` between sites, the constant sheaf on the source
is the pushforward along `G` of the constant sheaf on the target. -/
noncomputable def constantSheafContinuousIso
    {C D : Type (max u v)} [Category.{v} C] [Category.{v} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (G : C ⥤ D) [G.IsContinuous J K] [G.IsCocontinuous J K]
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)] [HasWeakSheafify K (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) :
    (constantSheaf J (ModuleCat.{max u v w} Λ)).obj M ≅
      (G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj
        ((constantSheaf K (ModuleCat.{max u v w} Λ)).obj M) :=
  (G.pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{max u v w} Λ) J K).app ((Functor.const Dᵒᵖ).obj M)

/-- The constant sheaf attached to a finitely generated module is locally constant of finite
type: the identity of any object is already a trivializing covering family. -/
lemma finiteTypeLocallyConstant_constantSheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) (hM : ModuleCat.isFG Λ M) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ
      ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M) := by
  intro X
  refine ⟨PUnit, fun _ => X, fun _ => 𝟙 X, ?_, fun _ =>
    ⟨M, hM, ⟨constantSheafOverIso J X M⟩⟩⟩
  apply J.superset_covering _ (J.top_mem X)
  intro Y f _
  simpa using (Sieve.ofArrows (fun _ : PUnit => X) (fun _ => 𝟙 X)).downward_closed
    (Sieve.ofArrows_mk _ _ PUnit.unit) f

/-- Local constancy of finite type passes to a slice site: the restriction to `C/U` of a locally
constant sheaf of finite type is again one. -/
lemma finiteTypeLocallyConstant_over
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (F : Sheaf J (ModuleCat.{max u v w} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F) (U : C) :
    IsFiniteTypeLocallyConstantModuleSheaf (J.over U) Λ
      ((J.overPullback (ModuleCat.{max u v w} Λ) U).obj F) := by
  intro V
  obtain ⟨I, W, f, hf, h⟩ := hF V.left
  let W' : I → Over U := fun i => Over.mk (f i ≫ V.hom)
  let f' : ∀ i, W' i ⟶ V := fun i => Over.homMk (f i)
  refine ⟨I, W', f', ?_, fun i => ?_⟩
  · rwa [J.mem_over_iff, Sieve.overEquiv_ofArrows]
  · obtain ⟨M, hM, ⟨e⟩⟩ := h i
    let G := (W' i).iteratedSliceForward
    have : G.IsContinuous ((J.over U).over (W' i)) (J.over (W i)) :=
      inferInstanceAs ((W' i).iteratedSliceForward.IsContinuous
        ((J.over U).over (W' i)) (J.over (W' i).left))
    have : G.IsCocontinuous ((J.over U).over (W' i)) (J.over (W i)) :=
      inferInstanceAs ((W' i).iteratedSliceForward.IsCocontinuous
        ((J.over U).over (W' i)) (J.over (W' i).left))
    let H := G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ)
      ((J.over U).over (W' i)) (J.over (W i))
    refine ⟨M, hM, ⟨constantSheafContinuousIso _ _ G M ≪≫ H.mapIso e ≪≫ ?_⟩⟩
    exact Iso.refl _

/-- If the cohomology sheaves of two of the three terms of a distinguished triangle lie in a weak
Serre class, so do those of the third. -/
lemma weakSerre_homology_obj₃
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (P : ObjectProperty A) [P.IsWeakSerreClass]
    (T : Triangle (DerivedCategory A))
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (h₁ : ∀ n, P ((DerivedCategory.homologyFunctor A n).obj T.obj₁))
    (h₂ : ∀ n, P ((DerivedCategory.homologyFunctor A n).obj T.obj₂)) :
    ∀ n, P ((DerivedCategory.homologyFunctor A n).obj T.obj₃) := by
  intro n
  exact ObjectProperty.prop_mid_of_exact₄ (P.prop_obj₂_of_exact)
    (by rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ T hT, Functor.map_zero])
    (DerivedCategory.HomologySequence.comp_δ T hT n (n + 1) rfl)
    (DerivedCategory.HomologySequence.δ_comp T hT n (n + 1) rfl)
    (DerivedCategory.HomologySequence.exact₂ T hT n)
    (DerivedCategory.HomologySequence.exact₃ T hT n (n + 1) rfl)
    (DerivedCategory.HomologySequence.exact₁ T hT n (n + 1) rfl)
    (h₁ n) (h₂ n) (h₁ (n + 1)) (h₂ (n + 1))

/-- The third term of a distinguished triangle is bounded below in degree `a` when the second is
and the first is bounded below in a strictly larger degree. -/
lemma isGE_obj₃_of_distinguished
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (T : Triangle (DerivedCategory A))
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (a b : ℤ) (hab : a < b) [T.obj₁.IsGE b] [T.obj₂.IsGE a] :
    T.obj₃.IsGE a := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_of_both_isZero
    (T.obj₂.isZero_of_isGE a i hi) (T.obj₁.isZero_of_isGE b (i + 1) (by omega))

/-- The third term of a distinguished triangle whose first map is surjective on degree-`b`
cohomology, and whose first two terms are bounded above by `b`, is bounded above by `b - 1`. -/
lemma isLE_obj₃_of_distinguished_of_epi
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
    (T : Triangle (DerivedCategory A))
    (hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles)
    (b : ℤ) [T.obj₁.IsLE b] [T.obj₂.IsLE b]
    [Epi ((DerivedCategory.homologyFunctor A b).map T.mor₁)] :
    T.obj₃.IsLE (b - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hepi : Epi ((DerivedCategory.homologyFunctor A i).map T.mor₁) := by
    by_cases h : i = b
    · subst i
      infer_instance
    · exact (T.obj₂.isZero_of_isLE b i (by omega)).epi _
  apply (DerivedCategory.HomologySequence.exact₃ T hT i (i + 1) rfl).isZero_X₂
  · exact (DerivedCategory.HomologySequence.exact₂ T hT i).epi_f_iff.mp hepi
  · exact (T.obj₁.isZero_of_isLE b (i + 1) (by omega)).eq_zero_of_tgt _

private lemma constantSheafOverIso_homEquiv
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) (F : Sheaf J (ModuleCat.{max u v w} Λ))
    (g : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj M ⟶ F) :
    ((constantSheafAdj (J.over U) (ModuleCat.{max u v w} Λ)
      (Over.mkIdTerminal (X := U))).homEquiv M _)
      ((constantSheafOverIso J U M).hom ≫ (J.overPullback (ModuleCat.{max u v w} Λ) U).map g) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (Opposite.op U) ≫
        g.hom.app (Opposite.op U) := by
  rw [Adjunction.homEquiv_unit]
  simp only [constantSheafAdj, Adjunction.comp_unit_app,
    constantPresheafAdj_unit_app]
  change (𝟙 M ≫ (toSheafify (J.over U)
    ((Functor.const (Over U)ᵒᵖ).obj M)).app (Opposite.op (Over.mk (𝟙 U)))) ≫
    ((constantSheafOverIso J U M).hom.hom.app (Opposite.op (Over.mk (𝟙 U))) ≫
      g.hom.app (Opposite.op U)) = _
  rw [Category.id_comp, ← Category.assoc]
  have h := congrArg (fun t => t.app (Opposite.op (Over.mk (𝟙 U))))
    ((Over.forget U).toSheafify_pullbackSheafificationCompatibility
      (ModuleCat.{max u v w} Λ) (J.over U) J ((Functor.const Cᵒᵖ).obj M))
  exact congrArg (fun t => t ≫ g.hom.app (Opposite.op U)) h

private lemma constantSheafOverIso_homEquiv_self
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) :
    ((constantSheafAdj (J.over U) (ModuleCat.{max u v w} Λ)
      (Over.mkIdTerminal (X := U))).homEquiv M _)
      (constantSheafOverIso J U M).hom =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) := by
  have h := constantSheafOverIso_homEquiv J U M
    ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj M) (𝟙 _)
  rw [(J.overPullback (ModuleCat.{max u v w} Λ) U).map_id, Category.comp_id] at h
  change _ = (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op U) at h
  exact h

private lemma fixedConstantMap_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {A B : ModuleCat.{max u v w} Λ}
    (φ : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj A ⟶
      (constantSheaf J (ModuleCat.{max u v w} Λ)).obj B) (t : A ⟶ B)
    (h : (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).map t ≫
        (constantSheafOverIso J U B).hom =
      (constantSheafOverIso J U A).hom ≫
        (J.overPullback (ModuleCat.{max u v w} Λ) U).map φ) :
    t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op U) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) ≫
        φ.hom.app (op U) := by
  let adj := constantSheafAdj (J.over U) (ModuleCat.{max u v w} Λ)
    (Over.mkIdTerminal (X := U))
  have hh := congrArg (adj.homEquiv A _) h
  rwa [adj.homEquiv_naturality_left, constantSheafOverIso_homEquiv_self,
    constantSheafOverIso_homEquiv] at hh

private lemma fixedConstantMap_of_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (U : C) [HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {A B : ModuleCat.{max u v w} Λ}
    (φ : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj A ⟶
      (constantSheaf J (ModuleCat.{max u v w} Λ)).obj B) (t : A ⟶ B)
    (h : t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op U) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) ≫
        φ.hom.app (op U)) :
    (constantSheaf (J.over U) (ModuleCat.{max u v w} Λ)).map t ≫
        (constantSheafOverIso J U B).hom =
      (constantSheafOverIso J U A).hom ≫
        (J.overPullback (ModuleCat.{max u v w} Λ) U).map φ := by
  let adj := constantSheafAdj (J.over U) (ModuleCat.{max u v w} Λ)
    (Over.mkIdTerminal (X := U))
  apply (adj.homEquiv A _).injective
  rw [adj.homEquiv_naturality_left, constantSheafOverIso_homEquiv,
    constantSheafOverIso_homEquiv_self]
  exact h

private lemma fixedConstantMap_sections_comp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    {A B : ModuleCat.{max u v w} Λ}
    (φ : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj A ⟶
      (constantSheaf J (ModuleCat.{max u v w} Λ)).obj B)
    (t : A ⟶ B) {U V : C} (k : V ⟶ U)
    (h : t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op U) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op U) ≫
        φ.hom.app (op U)) :
    t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op V) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op V) ≫
        φ.hom.app (op V) := by
  let ηA := toSheafify J ((Functor.const Cᵒᵖ).obj A)
  let ηB := toSheafify J ((Functor.const Cᵒᵖ).obj B)
  have hA : ηA.app (op V) = ηA.app (op U) ≫
      (((constantSheaf J (ModuleCat.{max u v w} Λ)).obj A).obj.map k.op) := by
    simpa [ηA, constantSheaf, presheafToSheaf, sheafify] using (ηA.naturality k.op)
  have hB : ηB.app (op V) = ηB.app (op U) ≫
      (((constantSheaf J (ModuleCat.{max u v w} Λ)).obj B).obj.map k.op) := by
    simpa [ηB, constantSheaf, presheafToSheaf, sheafify] using (ηB.naturality k.op)
  change t ≫ ηB.app (op V) = ηA.app (op V) ≫ φ.hom.app (op V)
  calc
    t ≫ ηB.app (op V) =
        (t ≫ ηB.app (op U)) ≫
          (((constantSheaf J (ModuleCat.{max u v w} Λ)).obj B).obj.map k.op) := by
      rw [hB, Category.assoc]
    _ = (ηA.app (op U) ≫ φ.hom.app (op U)) ≫
          (((constantSheaf J (ModuleCat.{max u v w} Λ)).obj B).obj.map k.op) := by
      rw [h]
    _ = ηA.app (op V) ≫ φ.hom.app (op V) := by
      rw [Category.assoc, ← φ.hom.naturality, ← Category.assoc, ← hA]

/-- Constant sheafification preserves epimorphisms of modules: both the constant-presheaf
functor and sheafification preserve finite colimits. -/
private lemma constantSheaf_map_epi
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    {E F : ModuleCat.{max u v w} Λ} (g : E ⟶ F) [Epi g] :
    Epi ((constantSheaf J (ModuleCat.{max u v w} Λ)).map g) := by
  have hp : PreservesFiniteColimits (constantSheaf J (ModuleCat.{max u v w} Λ)) := by
    rw [show constantSheaf J (ModuleCat.{max u v w} Λ) =
      (Functor.const Cᵒᵖ (C := ModuleCat.{max u v w} Λ)) ⋙
        presheafToSheaf J (ModuleCat.{max u v w} Λ) from rfl]
    have hps : PreservesColimitsOfSize.{0, 0}
        (presheafToSheaf J (ModuleCat.{max u v w} Λ)) :=
      (sheafificationAdjunction J (ModuleCat.{max u v w} Λ)).leftAdjoint_preservesColimits
    exact Limits.comp_preservesFiniteColimits _ _
  exact Functor.map_epi _ g

/-- A finitely generated module receives an epimorphism from a finite free module. -/
private lemma exists_freeMod_epi {Λ : Type w} [CommRing Λ] (E : ModuleCat.{max u v w} Λ)
    [Module.Finite Λ E] : ∃ (n : ℕ) (g : freeMod.{v, u, w} Λ n ⟶ E), Epi g := by
  obtain ⟨n, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.Finite.fg_top : (⊤ : Submodule Λ E).FG)
  refine ⟨n, ModuleCat.ofHom (Finsupp.linearCombination Λ s ∘ₗ
    (freeModEquiv.{v, u, w} Λ n).toLinearMap), (ModuleCat.epi_iff_surjective _).2 fun x => ?_⟩
  have hx : x ∈ Submodule.span Λ (Set.range s) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨a, ha⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  exact ⟨(freeModEquiv.{v, u, w} Λ n).symm a, by
    simpa [ModuleCat.hom_ofHom, Finsupp.linearCombination_apply] using ha⟩

/-- Over a covering family trivializing a locally constant sheaf of finite type, the trivializing
module receives a surjection from a finite free module with finitely generated kernel, and
that surjection stays surjective after applying the constant sheaf functor. -/
lemma exists_cover_constantFree_epi
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] [IsNoetherianRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (F : Sheaf J (ModuleCat.{max u v w} Λ))
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F)
    (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧
      ∀ i, ∃ (E : ModuleCat.{max u v w} Λ)
        (_e : (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj E ≅
          (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).obj F)
        (n : ℕ) (g : freeMod.{v, u, w} Λ n ⟶ E),
        Epi g ∧ Module.Finite Λ (LinearMap.ker g.hom) ∧
          Epi ((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).map g) := by
  obtain ⟨I, U, f, hcov, hloc⟩ := hF X
  refine ⟨I, U, f, hcov, fun i => ?_⟩
  obtain ⟨E, hE, ⟨e⟩⟩ := hloc i
  have : Module.Finite Λ E := (ModuleCat.isFG_iff E).mp hE
  obtain ⟨n, g, hg⟩ := exists_freeMod_epi.{v, u, w} E
  exact ⟨E, e, n, g, hg, Module.Finite.of_fg (Submodule.FG.of_le Module.Finite.fg_top le_top),
    constantSheaf_map_epi (J.over (U i)) Λ g⟩

/-- A covering sieve contains a covering family of arrows, indexed in `Type (max u v)`. -/
private lemma exists_ofArrows_mem_of_mem {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {X : C} {S : Sieve X} (hS : S ∈ J X) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i, S (f i) := by
  let I := Σ V : C, {f : V ⟶ X // S f}
  let U : I → C := fun i => i.1
  let f : ∀ i : I, U i ⟶ X := fun i => i.2.1
  refine ⟨I, U, f, J.superset_covering ?_ hS, fun i => i.2.2⟩
  intro V g hg
  exact Sieve.ofArrows_mk U f ⟨V, g, hg⟩

/-- A finite family of covering sieves is covered by the arrows of one covering family, each of
which lies in all the sieves. -/
private lemma exists_ofArrows_mem_of_forall_mem_fin {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) {X : C} {n : ℕ} (S : Fin n → Sieve X) (hS : ∀ j, S j ∈ J X) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i j, S j (f i) := by
  have : Finset.univ.inf S ∈ J X := Finset.inf_induction (p := (· ∈ J X)) (J.top_mem X)
    (fun _ h₁ _ h₂ => J.intersection_covering h₁ h₂) fun j _ => hS j
  obtain ⟨I, U, f, hf, hSf⟩ := exists_ofArrows_mem_of_mem J this
  exact ⟨I, U, f, hf, fun i j =>
    (Finset.inf_le (f := S) (Finset.mem_univ j) : Finset.univ.inf S ≤ S j) _ (hSf i)⟩

private lemma exists_cover_lift_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] {F G : Cᵒᵖ ⥤ ModuleCat.{max u v w} Λ}
    (φ : F ⟶ G) [Presheaf.IsLocallySurjective J φ]
    (X : C) (n : ℕ) (s : Fin n → G.obj (Opposite.op X)) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i, ∃ t : Fin n → F.obj (Opposite.op (U i)),
        ∀ j, φ.app (Opposite.op (U i)) (t j) = G.map (f i).op (s j) := by
  obtain ⟨I, U, f, hf, hSf⟩ := exists_ofArrows_mem_of_forall_mem_fin J
    (fun j => Presheaf.imageSieve φ (s j)) fun j => Presheaf.imageSieve_mem J φ (s j)
  exact ⟨I, U, f, hf, fun i => by choose t ht using hSf i; exact ⟨t, ht⟩⟩

/-- Equality after sheafification of two constant sections holds on a covering. -/
lemma exists_cover_eq_constant_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) (X : C) (x y : M)
    (h : (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) x =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) y) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ _i : I, x = y := by
  let S := Presheaf.equalizerSieve (F := (Functor.const Cᵒᵖ).obj M)
    (X := op X) x y
  have hS : S ∈ J X :=
    Presheaf.equalizerSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj M)) x y h
  obtain ⟨I, U, f, hf, hSf⟩ := exists_ofArrows_mem_of_mem J hS
  exact ⟨I, U, f, hf, fun i => by simpa [S, Presheaf.equalizerSieve_apply] using hSf i⟩

/-- A finite family of equalities after sheafification holds on one covering. -/
private lemma exists_cover_eq_constant_sections_fin
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    (M : ModuleCat.{max u v w} Λ) (X : C) (n : ℕ)
    (x y : Fin n → M)
    (h : ∀ j, (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) (x j) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj M)).app (op X) (y j)) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ _i : I, ∀ j, x j = y j := by
  obtain ⟨I, U, f, hf, hSf⟩ := exists_ofArrows_mem_of_forall_mem_fin J
    (fun j => Presheaf.equalizerSieve (F := (Functor.const Cᵒᵖ).obj M) (X := op X) (x j) (y j))
    fun j => Presheaf.equalizerSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj M))
      (x j) (y j) (h j)
  exact ⟨I, U, f, hf, fun i j => by simpa [Presheaf.equalizerSieve_apply] using hSf i j⟩

private lemma exists_cover_lift_free_sections
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] {F G : Cᵒᵖ ⥤ ModuleCat.{max u v w} Λ}
    (φ : F ⟶ G) [Presheaf.IsLocallySurjective J φ]
    (X : C) (n : ℕ) (s : freeMod.{v, u, w} Λ n ⟶ G.obj (Opposite.op X)) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧
        ∀ i, ∃ t : freeMod.{v, u, w} Λ n ⟶ F.obj (Opposite.op (U i)),
          t ≫ φ.app (Opposite.op (U i)) = s ≫ G.map (f i).op := by
  set s' : (Fin n →₀ Λ) →ₗ[Λ] (G.obj (Opposite.op X) : Type (max u v w)) :=
    s.hom ∘ₗ (freeModEquiv.{v, u, w} Λ n).symm.toLinearMap with hs'
  obtain ⟨I, U, f, hcov, ht⟩ :=
    exists_cover_lift_sections J φ X n (fun j => s' (Finsupp.single j 1))
  refine ⟨I, U, f, hcov, fun i => ?_⟩
  obtain ⟨t, ht⟩ := ht i
  refine ⟨ModuleCat.ofHom (Finsupp.linearCombination Λ t ∘ₗ
    (freeModEquiv.{v, u, w} Λ n).toLinearMap), ?_⟩
  have key : (φ.app (Opposite.op (U i))).hom ∘ₗ Finsupp.linearCombination Λ t =
      (G.map (f i).op).hom ∘ₗ s' := by
    apply Finsupp.lhom_ext
    intro j c
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_single]
    have hsm : (Finsupp.single j c : Fin n →₀ Λ) = c • Finsupp.single j 1 := by simp
    rw [hsm, map_smul, map_smul, map_smul]
    exact congrArg (fun y => c • y) (ht j)
  apply ModuleCat.hom_ext
  refine LinearMap.ext fun z => ?_
  obtain ⟨a, rfl⟩ := (freeModEquiv.{v, u, w} Λ n).symm.surjective z
  simpa [hs'] using congrArg (fun L => L a) key

/-- A morphism from a finite free constant module sheaf has fixed module coordinates
after passing to a covering. -/
private lemma exists_cover_fixed_constant_map_free
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (B : ModuleCat.{max u v w} Λ) (n : ℕ)
    (φ : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj
        (freeMod.{v, u, w} Λ n) ⟶
      (constantSheaf J (ModuleCat.{max u v w} Λ)).obj B) (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ t : freeMod.{v, u, w} Λ n ⟶ B,
          (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).map t ≫
              (constantSheafOverIso J (U i) B).hom =
            (constantSheafOverIso J (U i)
              (freeMod.{v, u, w} Λ n)).hom ≫
              (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map φ := by
  let A := freeMod.{v, u, w} Λ n
  let ηA := toSheafify J ((Functor.const Cᵒᵖ).obj A)
  let ηB := toSheafify J ((Functor.const Cᵒᵖ).obj B)
  let s : A ⟶ ((constantSheaf J (ModuleCat.{max u v w} Λ)).obj B).obj.obj (op X) :=
    ηA.app (op X) ≫ φ.hom.app (op X)
  obtain ⟨I, U, f, hf, ht⟩ := exists_cover_lift_free_sections J ηB X n s
  refine ⟨I, U, f, hf, fun i => ?_⟩
  obtain ⟨t, ht⟩ := ht i
  refine ⟨t, fixedConstantMap_of_sections J (U i) φ t ?_⟩
  change t ≫ ηB.app (op (U i)) = _
  rw [ht]
  dsimp [s]
  change ηA.app (op X) ≫ φ.hom.app (op X) ≫
      (((constantSheaf J (ModuleCat.{max u v w} Λ)).obj B).obj.map (f i).op) =
    ηA.app (op (U i)) ≫ φ.hom.app (op (U i))
  rw [← φ.hom.naturality]
  have hη := (ηA.naturality (f i).op).symm
  change ηA.app (op X) ≫
      (((constantSheaf J (ModuleCat.{max u v w} Λ)).obj A).obj.map (f i).op) =
    (𝟙 A) ≫ ηA.app (op (U i)) at hη
  simpa only [← Category.assoc, Category.id_comp] using congrArg
    (fun z => z ≫ φ.hom.app (op (U i))) hη

private lemma exists_moduleMap_factor_of_ker_le
    {Λ : Type w} [CommRing Λ] {F A B : ModuleCat.{m} Λ}
    (g : F ⟶ A) [Epi g] (t : F ⟶ B)
    (h : LinearMap.ker g.hom ≤ LinearMap.ker t.hom) :
    ∃ v : A ⟶ B, g ≫ v = t := by
  have hg : Function.Surjective g.hom :=
    (ModuleCat.epi_iff_surjective g).mp inferInstance
  let e := g.hom.quotKerEquivOfSurjective hg
  let v : A →ₗ[Λ] B :=
    ((LinearMap.ker g.hom).liftQ t.hom h).comp e.symm.toLinearMap
  refine ⟨ModuleCat.ofHom v, ?_⟩
  apply ModuleCat.hom_ext
  ext x
  simp [v, e, LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- A local section identity for `(constantSheaf J).map g ≫ φ`, rewritten through the
naturality of the sheafification unit so that it reads as an identity for `φ` precomposed
with `g`. -/
private lemma sections_comp_constantSheaf_map
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    {E A B : ModuleCat.{max u v w} Λ} (g : E ⟶ A)
    (φ : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj A ⟶
      (constantSheaf J (ModuleCat.{max u v w} Λ)).obj B) (W : C) (t : E ⟶ B)
    (h : t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op W) =
      (toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op W) ≫
        ((constantSheaf J (ModuleCat.{max u v w} Λ)).map g ≫ φ).hom.app (op W)) :
    t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op W) =
      (g ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj A)).app (op W)) ≫ φ.hom.app (op W) := by
  change t ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op W) =
    (toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op W) ≫
      (((constantSheaf J (ModuleCat.{max u v w} Λ)).map g).hom.app (op W) ≫
        φ.hom.app (op W)) at h
  rwa [← Category.assoc, ← constantSheaf_unit_naturality J g W] at h

/-- **A map of constant sheaves is locally induced by a map of modules.** A morphism from the
constant sheaf on a finitely generated module `A` to the constant sheaf on `B` agrees, over a
covering family, with the constant sheaf of a homomorphism `A ⟶ B`. This is the form in which
Stacks Tag 093S enters the induction. -/
lemma exists_cover_fixed_constant_map
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (A B : ModuleCat.{max u v w} Λ) (hA : ModuleCat.isFG Λ A)
    (φ : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj A ⟶
      (constantSheaf J (ModuleCat.{max u v w} Λ)).obj B) (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ t : A ⟶ B,
          (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).map t ≫
              (constantSheafOverIso J (U i) B).hom =
            (constantSheafOverIso J (U i) A).hom ≫
              (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map φ := by
  have : Module.Finite Λ A := (ModuleCat.isFG_iff A).mp hA
  obtain ⟨n, g, hg⟩ := exists_freeMod_epi.{v, u, w} A
  let ψ := (constantSheaf J (ModuleCat.{max u v w} Λ)).map g ≫ φ
  obtain ⟨I, U, f, hf, ht⟩ := exists_cover_fixed_constant_map_free J B n ψ X
  choose t ht using ht
  have hker : (LinearMap.ker g.hom).FG := Submodule.FG.of_le Module.Finite.fg_top le_top
  obtain ⟨m, r, hr⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hrel (i : I) (j : Fin m) :
      (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op (U i)) (t i (r j)) =
        (toSheafify J ((Functor.const Cᵒᵖ).obj B)).app (op (U i)) 0 := by
    have hj : g (r j) = 0 :=
      LinearMap.mem_ker.mp (hr ▸ Submodule.subset_span (Set.mem_range_self j))
    have hh := congrArg (fun z => z (r j)) (sections_comp_constantSheaf_map J g φ (U i) (t i)
      (fixedConstantMap_sections J (U i) ψ (t i) (ht i)))
    simpa only [ConcreteCategory.comp_apply, hj, map_zero] using hh
  have hrelations (i : I) :=
    exists_cover_eq_constant_sections_fin J B (U i) m (fun j => t i (r j)) (fun _ => 0) (hrel i)
  choose A' V k hcover hzero using hrelations
  have hfactor (i : I) (j : A' i) : ∃ v : A ⟶ B, g ≫ v = t i := by
    refine exists_moduleMap_factor_of_ker_le g (t i) ?_
    rw [← hr]
    exact Submodule.span_le.mpr (Set.range_subset_iff.2 fun l => hzero i j l)
  choose v hv using hfactor
  refine ⟨Σ i, A' i, (fun p => V p.1 p.2),
    (fun p => k p.1 p.2 ≫ f p.1),
    covering_ofArrows_comp J U f hf V k hcover, ?_⟩
  rintro ⟨i, j⟩
  refine ⟨v i j, ?_⟩
  apply fixedConstantMap_of_sections J (V i j) φ (v i j)
  apply (cancel_epi g).mp
  have hh := sections_comp_constantSheaf_map J g φ (V i j) (t i)
    (fixedConstantMap_sections_comp J ψ (t i) (k i j)
      (fixedConstantMap_sections J (U i) ψ (t i) (ht i)))
  rw [← hv i j] at hh
  simpa only [Category.assoc] using hh

private lemma exists_cover_lift_free_sheaf
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {F G : Sheaf J (ModuleCat.{max u v w} Λ)} (φ : F ⟶ G) [Epi φ]
    (X : C) (n : ℕ) (s : freeMod.{v, u, w} Λ n ⟶ G.obj.obj (Opposite.op X)) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ t : (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
            (freeMod.{v, u, w} Λ n) ⟶
          (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).obj F,
          t ≫ (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map φ =
            ((constantSheafAdj (J.over (U i)) (ModuleCat.{max u v w} Λ)
              (Over.mkIdTerminal (X := U i))).homEquiv
                (freeMod.{v, u, w} Λ n)
                ((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).obj G)).symm
                (s ≫ G.obj.map (f i).op) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (ModuleCat.{max u v w} Λ) φ).mpr inferInstance
  have : Presheaf.IsLocallySurjective J φ.hom := inferInstance
  obtain ⟨I, U, f, hcov, ht⟩ := exists_cover_lift_free_sections J φ.hom X n s
  refine ⟨I, U, f, hcov, fun i => ?_⟩
  obtain ⟨t, ht⟩ := ht i
  let adj := constantSheafAdj (J.over (U i)) (ModuleCat.{max u v w} Λ)
    (Over.mkIdTerminal (X := U i))
  refine ⟨(adj.homEquiv _ _).symm t, ?_⟩
  rw [← adj.homEquiv_naturality_right_symm]
  exact congrArg (adj.homEquiv _ _).symm ht

/-- Restriction of sheaves of modules to a slice site preserves zero morphisms. -/
lemma overPullback_preservesZeroMorphisms
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ] (U : C) :
    (J.overPullback (ModuleCat.{max u v w} Λ) U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

attribute [local instance] overPullback_preservesZeroMorphisms

private lemma exists_cover_lift_homology_generators
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ)
    (b : ℤ) (X : C) (n : ℕ)
    (s : freeMod.{v, u, w} Λ n ⟶ (T.homology b).obj.obj (op X)) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ (t : (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
            (freeMod.{v, u, w} Λ n) ⟶
          (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).obj (T.cycles b))
          (α : (HomologicalComplex.single _ (.up ℤ) b).obj
              ((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
                (freeMod.{v, u, w} Λ n)) ⟶
            ((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex (.up ℤ)).obj T),
          α.f b = (HomologicalComplex.singleObjXSelf _ _ _).hom ≫ t ≫
            (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map (T.iCycles b) ∧
          t ≫ (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map (T.homologyπ b) =
            ((constantSheafAdj (J.over (U i)) (ModuleCat.{max u v w} Λ)
              (Over.mkIdTerminal (X := U i))).homEquiv
                (freeMod.{v, u, w} Λ n)
                ((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).obj (T.homology b))).symm
                  (s ≫ (T.homology b).obj.map (f i).op) := by
  obtain ⟨I, U, f, hcov, ht⟩ :=
    exists_cover_lift_free_sheaf J (T.homologyπ b) X n s
  refine ⟨I, U, f, hcov, fun i => ?_⟩
  obtain ⟨t, ht⟩ := ht i
  let F := J.overPullback (ModuleCat.{max u v w} Λ) (U i)
  have hz (k : ℤ) (_ : (ComplexShape.up ℤ).Rel b k) :
      (t ≫ F.map (T.iCycles b)) ≫ F.map (T.d b k) = 0 := by
    rw [Category.assoc, ← F.map_comp, T.iCycles_d, F.map_zero, comp_zero]
  refine ⟨t, HomologicalComplex.mkHomFromSingle (t ≫ F.map (T.iCycles b)) hz, ?_, ht⟩
  simp only [HomologicalComplex.mkHomFromSingle_f, F]

/-- Local constancy of finite type is invariant under isomorphism of sheaves. -/
lemma finiteTypeLocallyConstant_of_iso
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {F G : Sheaf J (ModuleCat.{max u v w} Λ)} (e : F ≅ G)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ G := by
  intro X
  obtain ⟨I, U, f, hcov, h⟩ := hF X
  refine ⟨I, U, f, hcov, fun i => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h i
  exact ⟨M, hM, ⟨eM ≪≫ (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapIso e⟩⟩

private lemma exists_cover_constantComplex_representation_single
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (X : C) (F : Sheaf J (ModuleCat.{max u v w} Λ)) (b : ℤ)
    (hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧
      ∀ i, ∃ P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ,
        (∀ n, n ∉ Set.Icc b b → IsZero (P.X n)) ∧
        (∀ n, ModuleCat.isFG Λ (P.X n)) ∧
        Nonempty ((((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor _ b).obj F)) ≅
            (((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨I, U, f, hcov, h⟩ := hF X
  refine ⟨I, U, f, hcov, fun i => ?_⟩
  obtain ⟨M, hM, ⟨eM⟩⟩ := h i
  refine ⟨(CochainComplex.singleFunctor _ b).obj M, ?_, ?_, ?_⟩
  · intro n hn
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by simpa using hn)
  · intro n
    by_cases hn : n = b
    · subst n
      change ModuleCat.isFG Λ (((HomologicalComplex.single _ (.up ℤ) b).obj M).X b)
      simpa only [HomologicalComplex.single_obj_X_self] using hM
    · have hzero := HomologicalComplex.isZero_single_obj_X (.up ℤ) b M n hn
      rw [ModuleCat.isFG_iff]
      let : Subsingleton
          (((CochainComplex.singleFunctor (ModuleCat.{max u v w} Λ) b).obj M).X n) :=
        ModuleCat.isZero_iff_subsingleton.mp hzero
      infer_instance
  · exact ⟨(HomologicalComplex.singleMapHomologicalComplex
        (J.overPullback (ModuleCat.{max u v w} Λ) (U i)) (.up ℤ) b).app F ≪≫
      (CochainComplex.singleFunctor _ b).mapIso eM.symm ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex
        (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)) (.up ℤ) b).app M).symm⟩

/-- Stacks Tag 094G for an object concentrated in a single degree, in the form that carries an
explicit complex representative of the object. -/
lemma exists_cover_constantComplex_representation_of_isGE_of_isLE
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (Λ : Type w) [CommRing Λ]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    (X : C) (K : DerivedCategory (Sheaf J (ModuleCat.{max u v w} Λ)))
    (b : ℤ) [K.IsGE b] [K.IsLE b]
    (hK : IsFiniteTypeLocallyConstantModuleSheaf J Λ
      ((DerivedCategory.homologyFunctor (Sheaf J (ModuleCat.{max u v w} Λ)) b).obj K)) :
    ∃ (T : CochainComplex (Sheaf J (ModuleCat.{max u v w} Λ)) ℤ)
      (_e : K ≅ DerivedCategory.Q.obj T)
      (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧
        ∀ i, ∃ (P : CochainComplex (ModuleCat.{max u v w} Λ) ℤ),
          (∀ n, n ∉ Set.Icc b b → IsZero (P.X n)) ∧
          (∀ n, ModuleCat.isFG Λ (P.X n)) ∧
          Nonempty (DerivedCategory.Q.obj
            (((J.overPullback (ModuleCat.{max u v w} Λ) (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj T) ≅
            DerivedCategory.Q.obj
              (((constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj P)) := by
  obtain ⟨F, ⟨e⟩⟩ := K.exists_iso_singleFunctor_obj_of_isGE_of_isLE b
  have hF : IsFiniteTypeLocallyConstantModuleSheaf J Λ F :=
    finiteTypeLocallyConstant_of_iso J Λ
      ((DerivedCategory.homologyFunctor _ b).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso _ b).app F) hK
  obtain ⟨I, U, f, hcov, h⟩ :=
    exists_cover_constantComplex_representation_single J Λ X F b hF
  refine ⟨(CochainComplex.singleFunctor _ b).obj F, e, I, U, f, hcov, fun i => ?_⟩
  obtain ⟨P, hP, hfg, ⟨eP⟩⟩ := h i
  exact ⟨P, hP, hfg, ⟨DerivedCategory.Q.mapIso eP⟩⟩

/-- A map from a constant finite free sheaf into the target of an epimorphism of sheaves lifts,
over a covering family, to the source of that epimorphism. -/
lemma exists_cover_lift_constantFree
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {Λ : Type w} [CommRing Λ]
    [HasWeakSheafify J (ModuleCat.{max u v w} Λ)]
    [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{max u v w} Λ)]
    {F G : Sheaf J (ModuleCat.{max u v w} Λ)} (φ : F ⟶ G) [Epi φ]
    (n : ℕ) (g : (constantSheaf J (ModuleCat.{max u v w} Λ)).obj
      (freeMod.{v, u, w} Λ n) ⟶ G) (X : C) :
    ∃ (I : Type (max u v)) (U : I → C) (f : ∀ i, U i ⟶ X),
      Sieve.ofArrows U f ∈ J X ∧ ∀ i,
        ∃ t : (constantSheaf (J.over (U i)) (ModuleCat.{max u v w} Λ)).obj
            (freeMod.{v, u, w} Λ n) ⟶
          (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).obj F,
          t ≫ (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map φ =
            (constantSheafOverIso J (U i) (freeMod.{v, u, w} Λ n)).hom ≫
              (J.overPullback (ModuleCat.{max u v w} Λ) (U i)).map g := by
  let η := toSheafify J ((Functor.const Cᵒᵖ).obj (freeMod.{v, u, w} Λ n))
  obtain ⟨I, U, f, hf, ht⟩ := exists_cover_lift_free_sheaf J φ X n
    (η.app (op X) ≫ g.hom.app (op X))
  refine ⟨I, U, f, hf, fun i => ?_⟩
  obtain ⟨t, ht⟩ := ht i
  refine ⟨t, ht.trans ?_⟩
  apply ((constantSheafAdj (J.over (U i)) (ModuleCat.{max u v w} Λ)
    (Over.mkIdTerminal (X := U i))).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, constantSheafOverIso_homEquiv]
  simpa [η] using ((η ≫ g.hom).naturality (f i).op).symm

end Stacks.ConstantSheaf

end
