module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionOnComplexes
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite

/-!
# The structure-sheaf comparison in degree zero is pseudofunctorial

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (W, 𝒪_W)` be morphisms of ringed spaces.
`Stacks.RingedSpace.derivedPullbackSingleUnitIso h` is the identification
`ν_h : Lh^*(𝒪[0]) ≅ 𝒪[0]` of [Stacks, Tag 01CD], read in the derived category through
[Stacks, Tag 06YJ]. This file proves that `ν` is compatible with the composition isomorphism of
derived pullbacks of [Stacks, Tag 0D5S]:

`c_{f,g} ≫ ν_{f ≫ g} = Lf^*(ν_g) ≫ ν_f`.

## Main results

* `StacksDraft.UnitPullbackComposition.derivedPullbackSingleIso_comp`: the composition law
  for `Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso` at a flat module.
* `StacksDraft.UnitPullbackComposition.modulePullbackComp_hom_app_unit_comp`: the same
  compatibility for the undderived comparison `h^*𝒪 ≅ 𝒪` of [Stacks, Tag 01CD].
* `StacksDraft.UnitPullbackComposition.derivedPullbackCompIsoCanonical_hom_app_singleUnit`:
  **the coherence**, in degree `0`.

## Implementation notes

The composition law for the comparison `Lf^*(QP) ⟶ Q(f^*P)` at an arbitrary cochain complex is
`Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp`. What this file adds
is the passage from that comparison to `derivedPullbackSingleIso` — which is almost an identity,
because `DerivedCategory.singleFunctorIsoCompQ` is `Iso.refl` — its naturality in the complex,
the identification of the composition isomorphism on complexes at a single complex with `single`
of the module-level one, and the module-level coherence of the structure-sheaf comparison, which
is the mate statement `Stacks.PullbackTensorComposition.modulePullbackComp_unit` transposed.

*Why the composition algebra is lifted into `assoc_glue`.* `derivedPullback`,
`derivedPullbackComparison` and `derivedPullbackCompComparisonCanonical` are `abbrev`s, so `rw`,
which matches at reducible transparency, unfolds them and times out. Every step of the assembly
is therefore an `exact` against a lemma in which each object and morphism is a variable.

## References

* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical
  derivedPullbackCompComparisonCanonical derivedPullbackComparisonOnComplex)
open Stacks.RingedSpace (derivedPullbackSingleUnitIso)

universe u

namespace StacksDraft.UnitPullbackComposition

attribute [local instance] HasDerivedCategory.standard

/-! ### Two identities about single complexes -/

/-- The component of `DerivedCategory.singleFunctorIsoCompQh` is the inverse of
`DerivedCategory.quotientCompQhIso` at the single complex. -/
private lemma singleFunctorIsoCompQh_hom_app {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (n : ℤ) (F : C) :
    (DerivedCategory.singleFunctorIsoCompQh C n).hom.app F =
      (DerivedCategory.quotientCompQhIso C).inv.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj F) := by
  have h : (DerivedCategory.singleFunctorIsoCompQh C n).hom.app F =
      (DerivedCategory.quotientCompQhIso C).inv.app
        ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj F) ≫ 𝟙 _ := rfl
  rw [h, Category.comp_id]

/-- **The composition isomorphism on complexes, at a single complex.**  For additive functors
related by `e : F ⋙ G ≅ H`, the composition isomorphism on homological complexes, read at the
complex with `A` in degree `n`, is the two identifications of the degreewise image of a single
complex with a single complex, followed by `single` of the component of `e`. -/
private lemma mapHomologicalComplexCompIso_hom_app_single {ι : Type*} [DecidableEq ι]
    {V W W' : Type*} [Category* V] [Category* W] [Category* W']
    [Preadditive V] [Preadditive W] [Preadditive W']
    [HasZeroObject V] [HasZeroObject W] [HasZeroObject W']
    {F : V ⥤ W} {G : W ⥤ W'} {H : V ⥤ W'} (e : F ⋙ G ≅ H)
    [F.Additive] [G.Additive] [H.Additive] (c : ComplexShape ι) (n : ι) (A : V) :
    (Functor.mapHomologicalComplexCompIso e c).hom.app
          ((HomologicalComplex.single V c n).obj A) ≫
        (HomologicalComplex.singleMapHomologicalComplex H c n).hom.app A =
      (G.mapHomologicalComplex c).map
          ((HomologicalComplex.singleMapHomologicalComplex F c n).hom.app A) ≫
        (HomologicalComplex.singleMapHomologicalComplex G c n).hom.app (F.obj A) ≫
          (HomologicalComplex.single W' c n).map (e.hom.app A) := by
  ext i
  by_cases h : i = n
  · subst h
    have hnat := e.hom.naturality (HomologicalComplex.singleObjXSelf c i A).hom
    simp only [Functor.comp_map, Functor.comp_obj] at hnat
    simp [HomologicalComplex.single_map_f_self, reassoc_of% hnat]
  · simp [h]

/-! ### The comparison on complexes, and the single identification through it -/

section

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The comparison on complexes, assembled as a natural transformation `Q ⋙ Lf^* ⟶ f^* ⋙ Q`,
so that its naturality in the complex is available. -/
private def comparisonOnComplexNat :
    DerivedCategory.Q ⋙ derivedPullback f ⟶
      (modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso (ModuleSheaves Y)).inv
      (derivedPullback f) ≫
    Functor.whiskerLeft (HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ))
      (derivedPullbackComparison f) ≫
    Functor.whiskerRight (((modulePullback f).mapHomotopyCategoryFactors
      (ComplexShape.up ℤ)).hom) DerivedCategory.Qh ≫
    Functor.whiskerLeft ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom

private lemma comparisonOnComplexNat_app (P : CochainComplex (ModuleSheaves Y) ℤ) :
    (comparisonOnComplexNat f).app P = derivedPullbackComparisonOnComplex f P := rfl

/-- **Naturality of the comparison on complexes** in the complex. -/
theorem derivedPullbackComparisonOnComplex_naturality
    {P P' : CochainComplex (ModuleSheaves Y) ℤ} (φ : P ⟶ P') :
    (derivedPullback f).map (DerivedCategory.Q.map φ) ≫
        derivedPullbackComparisonOnComplex f P' =
      derivedPullbackComparisonOnComplex f P ≫
        DerivedCategory.Q.map (((modulePullback f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ) :=
  (comparisonOnComplexNat f).naturality φ

/-- `derivedPullbackSingleIso` is the comparison on complexes at the single complex, followed by
the identification of the degreewise pullback of a single complex with a single complex. -/
theorem derivedPullbackSingleIso_hom (F : ModuleSheaves Y)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F) :
    (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f F hF).hom =
      derivedPullbackComparisonOnComplex f
          ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj F) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
          (modulePullback f) (ComplexShape.up ℤ) 0).hom.app F) := by
  have h : (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f F hF).hom =
      (derivedPullback f).map ((DerivedCategory.singleFunctorIsoCompQh
          (ModuleSheaves Y) 0).hom.app F) ≫
        (derivedPullbackComparison f).app
            ((HomotopyCategory.quotient (ModuleSheaves Y) (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj F)) ≫
          DerivedCategory.Qh.map (((modulePullback f).mapHomotopyCategoryFactors
              (ComplexShape.up ℤ)).hom.app
              ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj F)) ≫
            (DerivedCategory.quotientCompQhIso (ModuleSheaves X)).hom.app
                (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj
                  ((HomologicalComplex.single (ModuleSheaves Y)
                    (ComplexShape.up ℤ) 0).obj F)) ≫
              DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
                (modulePullback f) (ComplexShape.up ℤ) 0).hom.app F) ≫ 𝟙 _ := rfl
  rw [h, Category.comp_id, singleFunctorIsoCompQh_hom_app]
  unfold derivedPullbackComparisonOnComplex
  simp only [Category.assoc]
  rfl

/-- `derivedPullbackSingleIso` followed by the degree-zero image of a module map. -/
private lemma derivedPullbackSingleIso_hom_comp (F : ModuleSheaves Y)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) F)
    {H : ModuleSheaves X} (α : (modulePullback f).obj F ⟶ H) :
    (Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f F hF).hom ≫
        (DerivedCategory.singleFunctor (ModuleSheaves X) 0).map α =
      derivedPullbackComparisonOnComplex f
          ((HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).obj F) ≫
        DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex
            (modulePullback f) (ComplexShape.up ℤ) 0).hom.app F ≫
          (HomologicalComplex.single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map α) := by
  rw [derivedPullbackSingleIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]
  rfl

end

/-! ### The module-level coherence of the maps to the structure sheaves -/

section UnitCoherence

variable {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ W)

/-- The canonical map `f^*𝒪_Y ⟶ 𝒪_X` transposes to the structure-sheaf map `f^♯`. -/
private lemma homEquiv_pullbackUnitToUnit :
    (modulePullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitToUnit f) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f) := by
  have h := homEquiv_map_comp_pullbackUnitToUnit f (SheafOfModules.unit (structureSheafRing Y))
    (𝟙 (SheafOfModules.unit (structureSheafRing Y)))
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
  exact h

/-- **The composition law for pullback is compatible with the maps to the structure sheaves.**
This is `RingedSpaceModuleAdjunction.modulePullbackCompUniq_hom_app_unit_comp` for the
composition isomorphism `Stacks.DerivedPullback.Composition.modulePullbackComp` that Tag 0D5S is
stated about, whose orientation is the opposite one.  Both composition isomorphisms are produced
by uniqueness of left adjoints, so the only handle on them is the mate correspondence; here it is
`Stacks.PullbackTensorComposition.modulePullbackComp_unit`, and the statement follows by
transposing both sides across `g^* ⊣ g_*` composed with `f^* ⊣ f_*`. -/
theorem modulePullbackComp_hom_app_unit_comp :
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app
          (SheafOfModules.unit (structureSheafRing W)) ≫
        pullbackUnitToUnit (f ≫ g) =
      (modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f := by
  refine (((modulePullbackPushforwardAdjunction g).comp
    (modulePullbackPushforwardAdjunction f)).homEquiv _ _).injective ?_
  have hL : (((modulePullbackPushforwardAdjunction g).comp
          (modulePullbackPushforwardAdjunction f)).homEquiv _ _)
        ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app
            (SheafOfModules.unit (structureSheafRing W)) ≫ pullbackUnitToUnit (f ≫ g)) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom (f ≫ g)) ≫
        (RingedSpaceModuleAdjunction.modulePushforwardComp f g).hom.app
          (SheafOfModules.unit (structureSheafRing X)) := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      ← Stacks.PullbackTensorComposition.modulePullbackComp_unit f g, Category.assoc,
      ← (RingedSpaceModuleAdjunction.modulePushforwardComp
          f g).inv.naturality (pullbackUnitToUnit (f ≫ g)), ← Category.assoc,
      ← Adjunction.homEquiv_unit, homEquiv_pullbackUnitToUnit]
    rfl
  have hR : (((modulePullbackPushforwardAdjunction g).comp
          (modulePullbackPushforwardAdjunction f)).homEquiv _ _)
        ((modulePullback f).map (pullbackUnitToUnit g) ≫ pullbackUnitToUnit f) =
      SheafOfModules.unitToPushforwardObjUnit (structureSheafHom g) ≫
        (modulePushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f)) := by
    rw [Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply]
    rw [homEquiv_map_comp_pullbackUnitToUnit f ((modulePullback g).obj
        (SheafOfModules.unit (structureSheafRing W))) (pullbackUnitToUnit g)]
    exact ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_right
        (pullbackUnitToUnit g)
        (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom f))).trans
      (by rw [homEquiv_pullbackUnitToUnit g]; rfl)
  rw [hL, hR]
  exact Category.comp_id _

end UnitCoherence

/-! ### The composition law for the degree-zero identification -/

section Assembly

variable {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ W)

/-- **The composition law at the level of cochain complexes.**  Given a compatible triple of
module maps `θ`, `α`, `β`, the composition isomorphism on complexes followed by the
single-complex identification for `f ≫ g` and by `α` is the single-complex identification for
`g` with `θ`, pulled back along `f`, then the one for `f` with `β`. -/
private lemma single_cplx_comp
    (F : ModuleSheaves W) (G : ModuleSheaves Y) (H : ModuleSheaves X)
    (θ : (modulePullback g).obj F ⟶ G)
    (α : (modulePullback (f ≫ g)).obj F ⟶ H) (β : (modulePullback f).obj G ⟶ H)
    (hαβ : (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app F ≫ α =
      (modulePullback f).map θ ≫ β) :
    (Functor.mapHomologicalComplexCompIso
            (Stacks.DerivedPullback.Composition.modulePullbackComp f g)
            (ComplexShape.up ℤ)).hom.app
          ((HomologicalComplex.single (ModuleSheaves W) (ComplexShape.up ℤ) 0).obj F) ≫
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback (f ≫ g))
            (ComplexShape.up ℤ) 0).hom.app F ≫
          (HomologicalComplex.single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map α) =
      ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex (modulePullback g)
              (ComplexShape.up ℤ) 0).hom.app F ≫
            (HomologicalComplex.single (ModuleSheaves Y) (ComplexShape.up ℤ) 0).map θ) ≫
        ((HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
            (ComplexShape.up ℤ) 0).hom.app G ≫
          (HomologicalComplex.single (ModuleSheaves X) (ComplexShape.up ℤ) 0).map β) := by
  have h1 := mapHomologicalComplexCompIso_hom_app_single
    (Stacks.DerivedPullback.Composition.modulePullbackComp f g) (ComplexShape.up ℤ) 0 F
  have h2 := (HomologicalComplex.singleMapHomologicalComplex (modulePullback f)
    (ComplexShape.up ℤ) 0).hom.naturality θ
  simp only [Functor.comp_map] at h2
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, h1]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp, hαβ, CategoryTheory.Functor.map_comp,
    ← reassoc_of% h2]

/-- Pure categorical bookkeeping: the shape in which the three compatibilities of the
composition law fit together.  Stated with every object and morphism a variable, so that it can
be applied by `exact` to a goal whose functors are reducible abbreviations. -/
private lemma assoc_glue {C : Type*} [Category* C]
    {A₀ A₁ A₂ A₃ A₄ A₅ A₆ A₇ : C}
    {u : A₀ ⟶ A₁} {k₁ : A₁ ⟶ A₂} {a : A₂ ⟶ A₃}
    {v : A₀ ⟶ A₄} {k₂ : A₄ ⟶ A₅} {p : A₅ ⟶ A₂}
    {q : A₅ ⟶ A₆} {r : A₆ ⟶ A₃}
    {w : A₄ ⟶ A₇} {k₃ : A₇ ⟶ A₆} {v' : A₀ ⟶ A₇}
    (h₁ : u ≫ k₁ = v ≫ k₂ ≫ p) (h₂ : p ≫ a = q ≫ r)
    (h₃ : w ≫ k₃ = k₂ ≫ q) (h₄ : v' = v ≫ w) :
    u ≫ k₁ ≫ a = v' ≫ k₃ ≫ r := by
  subst h₄
  rw [← Category.assoc, h₁]
  simp only [Category.assoc]
  rw [h₂, ← reassoc_of% h₃]

/-- **The composition law at the level of derived categories.**  The comparison of Tag 0D5S,
followed by the comparison on complexes for `f ≫ g` and a map `a`, is the comparison on
complexes for `g` with a map `φ`, pulled back along `f`, then the comparison on complexes for
`f` with a map `c`, as soon as the three maps are compatible on complexes. -/
private lemma derived_combined {P : CochainComplex (ModuleSheaves W) ℤ}
    {S : CochainComplex (ModuleSheaves Y) ℤ} {R : CochainComplex (ModuleSheaves X) ℤ}
    (a : ((modulePullback (f ≫ g)).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ R)
    (φ : ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj P ⟶ S)
    (c : ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj S ⟶ R)
    (hab : (Functor.mapHomologicalComplexCompIso
          (Stacks.DerivedPullback.Composition.modulePullbackComp f g)
          (ComplexShape.up ℤ)).hom.app P ≫ a =
      ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫ c) :
    (derivedPullbackCompComparisonCanonical f g).app (DerivedCategory.Q.obj P) ≫
        derivedPullbackComparisonOnComplex (f ≫ g) P ≫ DerivedCategory.Q.map a =
      (derivedPullback f).map (derivedPullbackComparisonOnComplex g P ≫
          DerivedCategory.Q.map φ) ≫
        derivedPullbackComparisonOnComplex f S ≫ DerivedCategory.Q.map c := by
  have hQ : DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
          (Stacks.DerivedPullback.Composition.modulePullbackComp f g)
          (ComplexShape.up ℤ)).hom.app P) ≫ DerivedCategory.Q.map a =
      DerivedCategory.Q.map (((modulePullback f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) ≫ DerivedCategory.Q.map c := by
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hab]
  exact assoc_glue
    (Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex_comp f g P) hQ
    (derivedPullbackComparisonOnComplex_naturality f φ)
    ((derivedPullback f).map_comp _ _)

/-- **The pseudofunctoriality of the degree-zero identification of Tag 06YJ.**  The composition
isomorphism of Tag 0D5S, followed by the identification of `L(f ≫ g)^*(F[0])` with a single
complex and by `α`, is the derived pullback along `f` of the identification for `g` with `θ`,
followed by the identification for `f` with `β`. -/
theorem derivedPullbackSingleIso_comp
    (F : ModuleSheaves W) (G : ModuleSheaves Y) (H : ModuleSheaves X)
    (hF : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := W.sheaf) F)
    (hG : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) G)
    (θ : (modulePullback g).obj F ⟶ G)
    (α : (modulePullback (f ≫ g)).obj F ⟶ H) (β : (modulePullback f).obj G ⟶ H)
    (hαβ : (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app F ≫ α =
      (modulePullback f).map θ ≫ β) :
    (derivedPullbackCompIsoCanonical f g).hom.app
          ((DerivedCategory.singleFunctor (ModuleSheaves W) 0).obj F) ≫
        ((Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso
            (f ≫ g) F hF).hom ≫
          (DerivedCategory.singleFunctor (ModuleSheaves X) 0).map α) =
      (derivedPullback f).map
          ((Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso g F hF).hom ≫
            (DerivedCategory.singleFunctor (ModuleSheaves Y) 0).map θ) ≫
        ((Stacks.Cohomology.FlatSingleDerivedPullback.derivedPullbackSingleIso f G hG).hom ≫
          (DerivedCategory.singleFunctor (ModuleSheaves X) 0).map β) := by
  rw [derivedPullbackSingleIso_hom_comp, derivedPullbackSingleIso_hom_comp,
    derivedPullbackSingleIso_hom_comp,
    Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical_hom]
  exact derived_combined f g _ _ _ (single_cplx_comp f g F G H θ α β hαβ)

end Assembly

/-! ### Tag 0G79 -/

section

variable {X Y W : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ W)
  [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology W.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology W.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- THE TARGET (verified to elaborate). -/
theorem derivedPullbackCompIsoCanonical_hom_app_singleUnit :
    (derivedPullbackCompIsoCanonical f g).hom.app
          ((DerivedCategory.singleFunctor (SheafOfModules.{u}
            (structureSheafRing W)) 0).obj
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf W.sheaf))) ≫
        (derivedPullbackSingleUnitIso (f ≫ g)).hom =
      (derivedPullback f).map (derivedPullbackSingleUnitIso g).hom ≫
        (derivedPullbackSingleUnitIso f).hom :=
  derivedPullbackSingleIso_comp f g _ _ _
    (Stacks.RingedSpace.isFlat_unit_of_ringedSpace W)
    (Stacks.RingedSpace.isFlat_unit_of_ringedSpace Y)
    (pullbackUnitToUnit g) (pullbackUnitToUnit (f ≫ g)) (pullbackUnitToUnit f)
    (StacksDraft.UnitPullbackComposition.modulePullbackComp_hom_app_unit_comp f g)

end

end StacksDraft.UnitPullbackComposition

end
