module

public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquareBaseChange
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquareCrossEffect
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSystem
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.EvaluationToDerivedColimit
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Adjunction.Whiskering

/-!
# Semilinear derived functors on arrows of modules

Let `A` be a commutative ring. The category `Arr(A)` of arrows `X₀ → X₁` of `A`-modules (the
functors `Fin 2 ⥤ ModuleCat A`) is abelian with enough projectives, and the simplicial derived
functors `LⱼΦ = Hⱼ(s(Φ(P)))` of `Stacks.SimplicialProjectiveResolution` apply to any functor
`Φ : Arr(A) ⥤ ModuleCat A`, for instance the exterior or tensor square of the source, of the
target or of the cokernel of an arrow. This file makes these derived functors functorial along
flat ring maps, so that they can be glued over the affine opens of a scheme.

**Projective arrows.** An arrow is projective exactly when it is a monomorphism with projective
source and projective cokernel; in particular evaluation at the source and at the target, and
the cokernel, preserve projective objects. Hence a simplicial projective resolution `P` of an
arrow `X` restricts to simplicial projective resolutions of `X₀` and `X₁`, the map between them
is degreewise split, and when `X` is a monomorphism the degreewise cokernel is a simplicial
projective resolution of the cokernel of `X`, through the long exact homology sequence.

**Semilinear functors.** A semilinear functor on arrows `Φ` is a functor `Φ_A` on `Arr(A)` for
every commutative ring `A`, with `A`-linear maps `σ_φ : Φ_A(φ^* Y) → φ^* Φ_B(Y)` for ring maps
`φ : A → B`, natural in `Y`, trivial for `φ = 𝟙` and transitive for composites; here `φ^*` is
restriction of scalars.

**Derived semilinear maps.** Let `φ : A → B` be flat, `f : X → φ^* Y` a morphism from an arrow of
`A`-modules to the restriction of an arrow of `B`-modules, and `P`, `Q` simplicial projective
resolutions of `X` and `Y`. A *semilinear lift* of `f` is a morphism `P → φ^* Q` of simplicial
arrows compatible with the augmentations. Semilinear lifts are the adjoints of lifts
`B ⊗_A P → Q` of the adjoint `B ⊗_A X → Y` of `f`, and `B ⊗_A P` is a simplicial projective
resolution of `B ⊗_A X` since `φ` is flat; so they exist and are unique up to simplicial
homotopy. Applying `Φ_A`, then `σ_φ`, and taking homology (restriction of scalars is exact) gives
a `φ`-semilinear map `Hⱼ(Φ_A(P)) → Hⱼ(Φ_B(Q))` which depends on no choice. These maps are
transitive along composites `A → B → C` of flat ring maps, are the derived maps for `φ = 𝟙`, are
compatible with the comparison isomorphisms between resolutions and with morphisms of semilinear
functors, and, when `Φ` commutes with flat base change on projective arrows and
`B ⊗_A X → Y` is an isomorphism, exhibit `Hⱼ(Φ_B(Q))` as the base change `B ⊗_A Hⱼ(Φ_A(P))`.

## Main definitions

* `CategoryTheory.ComposableArrows.cokernelFunctor`: the cokernel of an arrow, as a functor.
* `Stacks.SimplicialProjectiveResolution.leftResolution`,
  `Stacks.SimplicialProjectiveResolution.rightResolution`,
  `Stacks.SimplicialProjectiveResolution.cokernelResolution`: a simplicial projective resolution of
  an arrow evaluated at the source, at the target, and taken to cokernels, and
  `Stacks.SimplicialProjectiveResolution.simplicialHorseshoe` the resulting simplicial horseshoe.
* `Stacks.SimplicialProjectiveResolution.IsLiftAlong`: a morphism `P ⟶ G(Q)` lying over a morphism
  `X ⟶ G(Y)`, for a functor `G`.
* `Stacks.alternatingFaceMapHomologyMap`: the morphism `Hᵢ(s(K)) ⟶ H(Hᵢ(s(L)))` induced by
  `K ⟶ H(L)`, for a functor `H` preserving homology.
* `Stacks.restrictScalarsArrow`, `Stacks.extendScalarsArrow` and
  `Stacks.extendRestrictScalarsArrowAdj`: change of rings for arrows of modules.
* `Stacks.SemilinearArrowFunctor`: semilinear functors on arrows of modules, with their morphisms
  `Stacks.SemilinearArrowFunctor.Hom`, the base change morphism
  `Stacks.SemilinearArrowFunctor.baseChange` and the condition
  `Stacks.SemilinearArrowFunctor.HasFlatBaseChange`.
* `Stacks.SemilinearArrowFunctor.derivedMap` and
  `Stacks.SemilinearArrowFunctor.derivedSemilinearMap`: the derived semilinear maps, as `A`-linear
  maps into the restriction of scalars and as `φ`-semilinear maps.

## Main results

* `CategoryTheory.ComposableArrows.projective_iff`: an arrow is projective if and only if it is a
  monomorphism with projective source and projective cokernel.
* `CategoryTheory.ComposableArrows.enoughProjectives`: arrows in a category with enough
  projectives have enough projectives, so every arrow has a simplicial projective resolution.
* `Stacks.SimplicialProjectiveResolution.quasiIso_mapπ_cokernelFunctor`: for a resolution of a
  monomorphism, the degreewise cokernel resolves the cokernel.
* `Stacks.SemilinearArrowFunctor.derivedMap_eq`: the derived semilinear map is computed by any
  semilinear lift.
* `Stacks.SemilinearArrowFunctor.derivedMap_comp_restrictScalarsComp'_hom` and
  `Stacks.SemilinearArrowFunctor.derivedSemilinearMap_comp_apply`: transitivity.
* `Stacks.SemilinearArrowFunctor.derivedMap_id_comp_restrictScalarsId'_hom` and
  `Stacks.SemilinearArrowFunctor.derivedSemilinearMap_id_apply_self`: the identity.
* `Stacks.SemilinearArrowFunctor.derivedIso_hom_comp_derivedMap` and
  `Stacks.SemilinearArrowFunctor.derivedMap_comp_map_derivedIso_hom`: compatibility with the
  comparison isomorphisms between resolutions.
* `Stacks.SemilinearArrowFunctor.derivedHomologyMap_comp_derivedMap`: naturality in the
  semilinear functor.
* `Stacks.SemilinearArrowFunctor.isBaseChangeAlong_derivedSemilinearMap`: flat base change, for
  every flat ring map, localizations included.

## Implementation notes

The category of arrows is `ComposableArrows (ModuleCat A) 1`. Evaluation at the source and at the
target are exact, by the instances for evaluation functors. The semilinear structure of a
semilinear functor is an `A`-linear natural transformation into the restriction of scalars; its
compatibility with identities and composites is stated through the identifications
`ModuleCat.restrictScalarsId'` and `ModuleCat.restrictScalarsComp'` and their analogues for
arrows, which are the identity on elements. The derived semilinear map is defined as the base
change morphism `Hⱼ(Φ_A(P)) → φ^* Hⱼ(Φ_B(B ⊗_A P))` followed by the derived map of the adjoint
`B ⊗_A X → Y`, so that it involves no choice beyond that of a lift of `B ⊗_A X → Y`; that any
semilinear lift computes it is `Stacks.SemilinearArrowFunctor.derivedMap_eq`. Composites of ring
maps enter through a ring map `χ` together with a proof of `χ = φ ≫ ψ`, so that the
transitivity applies to composites which are only propositionally equal to a given ring map.

## References

* A. Dold, D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312.
* L. Illusie, *Complexe cotangent et déformations I*, Lecture Notes in Math. 239 (1971),
  chapitre I, §4.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Opposite Simplicial
open scoped TensorProduct

universe v u

/-! ### Projective arrows -/

namespace CategoryTheory.ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The cokernel of an arrow, as a functor on the category of arrows. -/
@[simps]
def cokernelFunctor : ComposableArrows C 1 ⥤ C where
  obj X := cokernel X.hom
  map {X Y} φ := cokernel.desc _ (app' φ 1 ≫ cokernel.π Y.hom)
    (by rw [← Category.assoc, naturality' φ 0 1, Category.assoc, cokernel.condition,
      Limits.comp_zero])
  map_id X := by
    refine coequalizer.hom_ext ?_
    simp only [cokernel.π_desc, Category.comp_id]
    exact Category.id_comp _
  map_comp φ ψ := by
    refine coequalizer.hom_ext ?_
    simp

/-- The cokernel functor is additive. -/
instance additive_cokernelFunctor : (cokernelFunctor (C := C)).Additive where
  map_add {X Y f g} := by
    change (cokernel.desc X.hom ((f + g).app 1 ≫ cokernel.π Y.hom) _ :
        cokernel X.hom ⟶ cokernel Y.hom) = cokernel.desc X.hom (f.app 1 ≫ cokernel.π Y.hom) _ +
      cokernel.desc X.hom (g.app 1 ≫ cokernel.π Y.hom) _
    refine coequalizer.hom_ext ?_
    simp [Preadditive.comp_add]

/-- The projection of the target of an arrow onto its cokernel, as a natural transformation. -/
@[simps]
def cokernelFunctorπ : (evaluation (Fin 2) C).obj 1 ⟶ cokernelFunctor where
  app X := cokernel.π (hom (n := 1) X)
  naturality _ _ _ := (cokernel.π_desc _ _ _).symm

/-- The arrow itself, as a natural transformation from the evaluation at the source to the
evaluation at the target. -/
abbrev evaluationHom : (evaluation (Fin 2) C).obj 0 ⟶ (evaluation (Fin 2) C).obj 1 :=
  (evaluation (Fin 2) C).map (homOfLE (by decide))

/-- An arrow composed with the projection onto its cokernel is zero, as natural
transformations. -/
@[reassoc (attr := simp)]
lemma evaluationHom_comp_cokernelFunctorπ :
    evaluationHom (C := C) ≫ cokernelFunctorπ = 0 := by
  ext X
  exact cokernel.condition (hom (n := 1) X)

/-- A morphism of arrows with epimorphic components is an epimorphism. -/
private lemma epi_homMk₁ {F G : ComposableArrows C 1} (a : F.obj' 0 ⟶ G.obj' 0)
    (b : F.obj' 1 ⟶ G.obj' 1) (w : F.map' 0 1 ≫ b = a ≫ G.map' 0 1) (ha : Epi a) (hb : Epi b) :
    Epi (homMk₁ a b w) := by
  rw [NatTrans.epi_iff_epi_app' C]
  intro i
  fin_cases i
  exacts [ha, hb]

/-- **Projective arrows.** An arrow which is a monomorphism with projective source and projective
cokernel is a projective object of the category of arrows. -/
theorem projective_of_mono (X : ComposableArrows C 1) [Mono X.hom] [Projective X.left]
    [Projective (cokernel X.hom)] : Projective X := by
  let S := ShortComplex.mk X.hom (cokernel.π X.hom) (cokernel.condition _)
  let sp : S.Splitting := ShortComplex.Splitting.ofExactOfSection S
    (S.exact_of_g_is_cokernel (cokernelIsCokernel X.hom))
    (Projective.factorThru (𝟙 _) (cokernel.π X.hom)) (Projective.factorThru_comp _ _)
    (inferInstanceAs (Mono X.hom))
  refine ⟨fun {E Z} f e he => ?_⟩
  have he' := (NatTrans.epi_iff_epi_app' C e).1 he
  have : Epi (e.app 0) := he' _
  have : Epi (e.app 1) := he' _
  obtain ⟨a, ha⟩ := Projective.factors (P := X.left) (f.app 0) (e.app 0)
  obtain ⟨b, hb⟩ := Projective.factors (P := cokernel X.hom) (sp.s ≫ f.app 1) (e.app 1)
  have hid : sp.r ≫ X.hom + cokernel.π X.hom ≫ sp.s = 𝟙 _ := sp.id
  have hr : X.hom ≫ sp.r = 𝟙 _ := sp.f_r
  refine ⟨homMk₁ a ((sp.r ≫ a ≫ E.hom : X.right ⟶ E.right) +
    (cokernel.π X.hom ≫ b : X.right ⟶ E.right)) ?_, ?_⟩
  · show X.hom ≫ _ = a ≫ E.hom
    simp [Preadditive.comp_add, reassoc_of% hr]
  · refine hom_ext₁ ha ?_
    show ((sp.r ≫ a ≫ E.hom : X.right ⟶ E.right) +
      (cokernel.π X.hom ≫ b : X.right ⟶ E.right)) ≫ e.app 1 = f.app 1
    have he₁ : E.hom ≫ e.app 1 = e.app 0 ≫ Z.hom := e.naturality _
    have hf₁ : X.hom ≫ f.app 1 = f.app 0 ≫ Z.hom := f.naturality _
    rw [Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc, hb,
      he₁, reassoc_of% ha, ← hf₁, ← Category.assoc,
      ← Category.assoc, ← Preadditive.add_comp, hid, Category.id_comp]

/-- The source of a projective arrow is projective. -/
theorem projective_left (X : ComposableArrows C 1) [Projective X] : Projective X.left := by
  refine ⟨fun {E Z} f e he => ?_⟩
  let e' : mk₁ (0 : E ⟶ X.right) ⟶ mk₁ (0 : Z ⟶ X.right) := homMk₁ e (𝟙 _) (by simp)
  have : Epi e' := epi_homMk₁ _ _ _ ‹_› inferInstance
  obtain ⟨g, hg⟩ := Projective.factors (homMk₁ f 0 (by simp) : X ⟶ mk₁ (0 : Z ⟶ X.right)) e'
  exact ⟨g.app 0, congrArg (fun φ => φ.app 0) hg⟩

/-- The target of a projective arrow is projective. -/
theorem projective_right (X : ComposableArrows C 1) [Projective X] : Projective X.right := by
  refine ⟨fun {E Z} f e he => ?_⟩
  let e' : mk₁ (𝟙 E) ⟶ mk₁ (𝟙 Z) := homMk₁ e e (by simp)
  have : Epi e' := epi_homMk₁ _ _ _ ‹_› ‹_›
  obtain ⟨g, hg⟩ := Projective.factors (homMk₁ (X.hom ≫ f) f (by simp) : X ⟶ mk₁ (𝟙 Z)) e'
  exact ⟨g.app 1, congrArg (fun φ => φ.app 1) hg⟩

/-- **The map of a projective arrow is a split monomorphism.** Lift the identity along the
epimorphism `(X₀ → X₀ ⊞ X₁) ⟶ X` given by `𝟙` and `(X.hom, 𝟙)`. -/
theorem isSplitMono_hom (X : ComposableArrows C 1) [Projective X] : IsSplitMono X.hom := by
  let e : mk₁ (biprod.inl : X.left ⟶ X.left ⊞ X.right) ⟶ X :=
    homMk₁ (𝟙 _) (biprod.desc X.hom (𝟙 _)) (by simp)
  have : Epi e :=
    epi_homMk₁ _ _ _ inferInstance (epi_of_epi_fac (f := biprod.inr) (biprod.inr_desc _ _))
  obtain ⟨s, hs⟩ := Projective.factors (𝟙 X) e
  have h₀ : s.app 0 = 𝟙 X.left := (Category.comp_id _).symm.trans (congrArg (fun φ => φ.app 0) hs)
  refine IsSplitMono.mk' ⟨s.app 1 ≫ biprod.fst, ?_⟩
  have h : X.hom ≫ s.app 1 = s.app 0 ≫ biprod.inl := s.naturality _
  rw [← Category.assoc, h, h₀]
  simp

/-- The cokernel of a projective arrow is projective. -/
theorem projective_cokernel (X : ComposableArrows C 1) [Projective X] :
    Projective (cokernel X.hom) := by
  refine ⟨fun {E Z} f e he => ?_⟩
  let e' : mk₁ (0 : X.left ⟶ E) ⟶ mk₁ (0 : X.left ⟶ Z) := homMk₁ (𝟙 _) e (by simp)
  have : Epi e' := epi_homMk₁ _ _ _ inferInstance ‹_›
  obtain ⟨g, hg⟩ := Projective.factors
    (homMk₁ (𝟙 _) (cokernel.π X.hom ≫ f) (by simp) : X ⟶ mk₁ (0 : X.left ⟶ Z)) e'
  have hg₁ : g.app 1 ≫ e = cokernel.π X.hom ≫ f := congrArg (fun φ => φ.app 1) hg
  have hw : X.hom ≫ g.app 1 = 0 := (g.naturality _).trans Limits.comp_zero
  exact ⟨cokernel.desc _ (g.app 1) hw, coequalizer.hom_ext (by simpa using hg₁)⟩

/-- **Projective arrows**, characterized: an arrow is a projective object of the category of
arrows if and only if it is a monomorphism with projective source and projective cokernel. -/
theorem projective_iff (X : ComposableArrows C 1) :
    Projective X ↔ Projective X.left ∧ Mono X.hom ∧ Projective (cokernel X.hom) :=
  ⟨fun _ => ⟨projective_left X, (isSplitMono_hom X).mono, projective_cokernel X⟩,
    fun ⟨_, _, _⟩ => projective_of_mono X⟩

/-- Evaluation at the source preserves projective objects. -/
instance preservesProjectiveObjects_evaluation_zero :
    ((evaluation (Fin 2) C).obj 0).PreservesProjectiveObjects :=
  ⟨fun {X} _ => projective_left X⟩

/-- Evaluation at the target preserves projective objects. -/
instance preservesProjectiveObjects_evaluation_one :
    ((evaluation (Fin 2) C).obj 1).PreservesProjectiveObjects :=
  ⟨fun {X} _ => projective_right X⟩

/-- The cokernel functor preserves projective objects. -/
instance preservesProjectiveObjects_cokernelFunctor :
    (cokernelFunctor (C := C)).PreservesProjectiveObjects :=
  ⟨fun {X} _ => projective_cokernel X⟩

/-- **The category of arrows has enough projectives** when `C` has. -/
instance enoughProjectives [EnoughProjectives C] : EnoughProjectives (ComposableArrows C 1) :=
  Stacks.CategoryHomology.diagramsEnoughProjectives _ _

end CategoryTheory.ComposableArrows

/-! ### Simplicial projective resolutions of arrows -/

namespace Stacks.SimplicialProjectiveResolution

open ComposableArrows

variable {C : Type u} [Category.{v} C] [Abelian C] {X : ComposableArrows C 1}

/-- A simplicial projective resolution of an arrow, evaluated at the source: a simplicial
projective resolution of the source. -/
abbrev leftResolution (P : SimplicialProjectiveResolution X) :
    SimplicialProjectiveResolution X.left :=
  P.map ((evaluation (Fin 2) C).obj 0)

/-- A simplicial projective resolution of an arrow, evaluated at the target: a simplicial
projective resolution of the target. -/
abbrev rightResolution (P : SimplicialProjectiveResolution X) :
    SimplicialProjectiveResolution X.right :=
  P.map ((evaluation (Fin 2) C).obj 1)

/-- The morphism from the resolution of the source to the resolution of the target given in each
degree by the arrow `Pₙ`. -/
def leftToRight (P : SimplicialProjectiveResolution X) :
    P.leftResolution.obj ⟶ P.rightResolution.obj :=
  Functor.whiskerLeft P.obj evaluationHom

/-- The morphism `leftToRight` is given in each degree by the arrow `Pₙ`. -/
lemma leftToRight_app (P : SimplicialProjectiveResolution X) (n : SimplexCategoryᵒᵖ) :
    P.leftToRight.app n = (P.obj.obj n).hom :=
  rfl

/-- The morphism `leftToRight` lies over the arrow `X.hom`. -/
lemma isLift_leftToRight (P : SimplicialProjectiveResolution X) :
    IsLift P.leftResolution P.rightResolution X.hom P.leftToRight := by
  rw [isLift_iff, mapOfQuasiIso_ε, mapOfQuasiIso_ε]
  exact P.ε.naturality _

/-- **A resolution of an arrow is degreewise split**: its terms are projective arrows, which are
split monomorphisms. -/
instance isSplitMono_leftToRight_app (P : SimplicialProjectiveResolution X)
    (n : SimplexCategoryᵒᵖ) : IsSplitMono (P.leftToRight.app n) :=
  have : Projective (P.obj.obj n) := P.projective n.unop.len
  isSplitMono_hom (P.obj.obj n)

/-- The degreewise cokernel sequence `0 → P₀ → P₁ → coker → 0` of a simplicial projective
resolution of an arrow. -/
abbrev cokernelSequence (P : SimplicialProjectiveResolution X) :
    ShortComplex (SimplicialObject C) :=
  ShortComplex.mk P.leftToRight (Functor.whiskerLeft P.obj cokernelFunctorπ)
    (by ext n : 2; exact cokernel.condition _)

/-- The degreewise cokernel sequence is short exact in each degree. -/
lemma shortExact_cokernelSequence_app (P : SimplicialProjectiveResolution X)
    (n : SimplexCategoryᵒᵖ) :
    (P.cokernelSequence.map ((evaluation SimplexCategoryᵒᵖ C).obj n)).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact (P.leftToRight.app n)
    mono_f := (isSplitMono_leftToRight_app P n).mono
    epi_g := inferInstanceAs (Epi (cokernel.π (P.leftToRight.app n))) }

/-- The alternating face map complexes of the degreewise cokernel sequence form a short exact
sequence. -/
lemma shortExact_cokernelSequence_map (P : SimplicialProjectiveResolution X) :
    (P.cokernelSequence.map (alternatingFaceMapComplex C)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n =>
    P.shortExact_cokernelSequence_app (op ⦋n⦌)

/-- For a simplicial projective resolution of a monomorphism, the degreewise cokernel is a
resolution of the cokernel: by the long exact homology sequence of the degreewise cokernel
sequence. -/
instance quasiIso_mapπ_cokernelFunctor [Mono X.hom] (P : SimplicialProjectiveResolution X) :
    QuasiIso (P.mapπ cokernelFunctor) := by
  let S : ShortComplex C := ShortComplex.mk X.hom (cokernel.π X.hom) (cokernel.condition _)
  have hS : S.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact X.hom
      mono_f := inferInstanceAs (Mono X.hom)
      epi_g := inferInstanceAs (Epi (cokernel.π X.hom)) }
  let φ : P.cokernelSequence.map (alternatingFaceMapComplex C) ⟶
      S.map (ChainComplex.single₀ C) :=
    { τ₁ := P.leftResolution.π
      τ₂ := P.rightResolution.π
      τ₃ := P.mapπ cokernelFunctor
      comm₁₂ := P.isLift_leftToRight.symm
      comm₂₃ := HomologicalComplex.to_single_hom_ext (by
        change (P.mapπ ((evaluation (Fin 2) C).obj 1)).f 0 ≫
            ((ChainComplex.single₀ C).map (cokernel.π X.hom)).f 0 =
          (Functor.whiskerLeft P.obj cokernelFunctorπ).app (op ⦋0⦌) ≫
            (P.mapπ cokernelFunctor).f 0
        rw [mapπ_f_zero, mapπ_f_zero, ChainComplex.single₀_map_f_zero]
        exact cokernelFunctorπ.naturality P.ε) }
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ P.shortExact_cokernelSequence_map
    (hS.map_of_exact _) (inferInstanceAs (QuasiIso (P.mapπ _)))
    (inferInstanceAs (QuasiIso (P.mapπ _)))

/-- A simplicial projective resolution of a monomorphism, taken degreewise to cokernels: a
simplicial projective resolution of the cokernel. -/
abbrev cokernelResolution [Mono X.hom] (P : SimplicialProjectiveResolution X) :
    SimplicialProjectiveResolution (cokernel X.hom) :=
  P.mapOfQuasiIso cokernelFunctor (fun _ => cokernelFunctor.projective_obj _) inferInstance

/-- The morphism from the resolution of the target to the resolution of the cokernel given in
each degree by the projection onto the cokernel of the arrow `Pₙ`. -/
def rightToCokernel [Mono X.hom] (P : SimplicialProjectiveResolution X) :
    P.rightResolution.obj ⟶ P.cokernelResolution.obj :=
  Functor.whiskerLeft P.obj cokernelFunctorπ

/-- The morphism `rightToCokernel` lies over the projection onto the cokernel. -/
lemma isLift_rightToCokernel [Mono X.hom] (P : SimplicialProjectiveResolution X) :
    IsLift P.rightResolution P.cokernelResolution (cokernel.π X.hom) P.rightToCokernel := by
  refine (isLift_iff _ _).2 ?_
  have h₁ : P.cokernelResolution.ε = cokernelFunctor.map P.ε := mapOfQuasiIso_ε _ _ _ _
  have h₂ : P.rightResolution.ε = ((evaluation (Fin 2) C).obj 1).map P.ε :=
    mapOfQuasiIso_ε _ _ _ _
  exact (congrArg (P.rightToCokernel.app (op ⦋0⦌) ≫ ·) h₁).trans
    ((cokernelFunctorπ.naturality P.ε).symm.trans (congrArg (· ≫ cokernel.π X.hom) h₂.symm))

/-- The degreewise cokernel sequence of a simplicial projective resolution of an arrow is a short
exact sequence of simplicial objects. -/
lemma shortExact_cokernelSequence (P : SimplicialProjectiveResolution X) :
    P.cokernelSequence.ShortExact := by
  have hP := P.shortExact_cokernelSequence_app
  have : ∀ n, Mono (P.cokernelSequence.f.app n) := fun n => (hP n).mono_f
  have : ∀ n, Epi (P.cokernelSequence.g.app n) := fun n => (hP n).epi_g
  have : Mono P.cokernelSequence.f := NatTrans.mono_of_mono_app _
  have : Epi P.cokernelSequence.g := NatTrans.epi_of_epi_app _
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun n => ?_
  exact IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).1 (hP n).exact)
    (P.cokernelSequence.mapHomologyIso ((evaluation SimplexCategoryᵒᵖ C).obj n)).symm

/-- **The simplicial horseshoe of a resolution of a monomorphism.** A simplicial projective
resolution `P` of a monomorphism `X₀ ⟶ X₁` gives the simplicial horseshoe
`0 → P₀ → P₁ → coker → 0` over the short exact sequence `0 → X₀ → X₁ → coker → 0`. -/
def simplicialHorseshoe [Mono X.hom] (P : SimplicialProjectiveResolution X) :
    SimplicialHorseshoe (ShortComplex.mk X.hom (cokernel.π X.hom) (cokernel.condition _)) where
  P₁ := P.leftResolution
  P₂ := P.rightResolution
  P₃ := P.cokernelResolution
  f := P.leftToRight
  g := P.rightToCokernel
  w := P.cokernelSequence.zero
  shortExact := P.shortExact_cokernelSequence
  isLift_f := P.isLift_leftToRight
  isLift_g := P.isLift_rightToCokernel

end Stacks.SimplicialProjectiveResolution

/-! ### Lifts along a functor -/

namespace Stacks.SimplicialProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] {C' : Type*} [Category C'] [Abelian C']
  {C'' : Type*} [Category C''] [Abelian C'']

/-- A morphism `f : P ⟶ G(Q)` of simplicial objects, from a simplicial projective resolution `P`
of `X` to the image under a functor `G` of a simplicial projective resolution `Q` of `Y`, *lies
over* `g : X ⟶ G(Y)` if it is compatible with the augmentations. For `G` the identity this is
`IsLift`; for `G` a restriction of scalars it is a semilinear lift. -/
def IsLiftAlong (G : C' ⥤ C) {X : C} {Y : C'} (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (g : X ⟶ G.obj Y) (f : P.obj ⟶ Q.obj ⋙ G) : Prop :=
  f.app (op ⦋0⦌) ≫ G.map Q.ε = P.ε ≫ g

variable {G : C' ⥤ C} {X X₀ : C} {Y Y' : C'} {P : SimplicialProjectiveResolution X}
  {Q : SimplicialProjectiveResolution Y}

/-- Precomposing a lift along `G` with a lift is a lift along `G` of the composite. -/
lemma IsLift.comp_isLiftAlong {P₀ : SimplicialProjectiveResolution X₀} {g₀ : X₀ ⟶ X}
    {k : P₀.obj ⟶ P.obj} {g : X ⟶ G.obj Y} {f : P.obj ⟶ Q.obj ⋙ G} (hk : IsLift P₀ P g₀ k)
    (hf : IsLiftAlong G P Q g f) : IsLiftAlong G P₀ Q (g₀ ≫ g) (k ≫ f) := by
  rw [isLift_iff] at hk
  unfold IsLiftAlong at hf ⊢
  rw [NatTrans.comp_app, Category.assoc, hf, reassoc_of% hk]

/-- Postcomposing a lift along `G` with the image under `G` of a lift is a lift along `G` of the
composite. -/
lemma IsLiftAlong.comp_whiskerRight {Q' : SimplicialProjectiveResolution Y'} {g : X ⟶ G.obj Y}
    {f : P.obj ⟶ Q.obj ⋙ G} {g' : Y ⟶ Y'} {k : Q.obj ⟶ Q'.obj} (hf : IsLiftAlong G P Q g f)
    (hk : IsLift Q Q' g' k) :
    IsLiftAlong G P Q' (g ≫ G.map g') (f ≫ Functor.whiskerRight k G) := by
  rw [isLift_iff] at hk
  unfold IsLiftAlong at hf ⊢
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc, ← G.map_comp, hk, G.map_comp,
    reassoc_of% hf]

/-- Composites of lifts along functors are lifts along the composite functor. -/
lemma IsLiftAlong.comp {G' : C'' ⥤ C'} {Z : C''} {S : SimplicialProjectiveResolution Z}
    {g : X ⟶ G.obj Y} {f : P.obj ⟶ Q.obj ⋙ G} {g' : Y ⟶ G'.obj Z} {f' : Q.obj ⟶ S.obj ⋙ G'}
    (hf : IsLiftAlong G P Q g f) (hf' : IsLiftAlong G' Q S g' f') :
    IsLiftAlong (G' ⋙ G) P S (g ≫ G.map g') (f ≫ Functor.whiskerRight f' G) := by
  unfold IsLiftAlong at hf hf' ⊢
  rw [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc, Functor.comp_map,
    ← G.map_comp, hf', G.map_comp, reassoc_of% hf]

/-- Postcomposing a lift along `G` with a natural transformation `τ : G ⟶ G'` gives a lift along
`G'`. -/
lemma IsLiftAlong.comp_whiskerLeft {G' : C' ⥤ C} {g : X ⟶ G.obj Y} {f : P.obj ⟶ Q.obj ⋙ G}
    (hf : IsLiftAlong G P Q g f) (τ : G ⟶ G') :
    IsLiftAlong G' P Q (g ≫ τ.app Y) (f ≫ Functor.whiskerLeft Q.obj τ) := by
  unfold IsLiftAlong at hf ⊢
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc, ← τ.naturality,
    reassoc_of% hf]

/-- **Lifts along a right adjoint.** For an adjunction `F ⊣ G` and a simplicial projective
resolution `P` of `X` whose image under `F` is a simplicial projective resolution of `F(X)`, a
morphism `f : F(P) ⟶ Q` lies over the adjoint `F(X) ⟶ Y` of `g : X ⟶ G(Y)` if and only if its
adjoint `P ⟶ G(Q)` lies along `G` over `g`. -/
lemma isLift_iff_isLiftAlong {F : C ⥤ C'} [F.Additive] (adj : F ⊣ G)
    (P : SimplicialProjectiveResolution X) (hP : ∀ n, Projective (F.obj (P.obj _⦋n⦌)))
    (hπ : QuasiIso (P.mapπ F)) (Q : SimplicialProjectiveResolution Y) (g : X ⟶ G.obj Y)
    (f : P.obj ⋙ F ⟶ Q.obj) :
    IsLift (P.mapOfQuasiIso F hP hπ) Q ((adj.homEquiv _ _).symm g) f ↔
      IsLiftAlong G P Q g ((adj.whiskerRight SimplexCategoryᵒᵖ).homEquiv P.obj Q.obj f) := by
  refine (isLift_iff _ _).trans ?_
  unfold IsLiftAlong
  have hε : (P.mapOfQuasiIso F hP hπ).ε = F.map P.ε := mapOfQuasiIso_ε F P hP hπ
  have h₁ : ((adj.whiskerRight SimplexCategoryᵒᵖ).homEquiv P.obj Q.obj f).app (op ⦋0⦌) ≫
      G.map Q.ε = adj.homEquiv _ _ (f.app (op ⦋0⦌) ≫ Q.ε) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, NatTrans.comp_app,
      Adjunction.whiskerRight_unit_app_app, G.map_comp, Category.assoc]
    rfl
  have h₂ : P.ε ≫ g = adj.homEquiv _ _ (F.map P.ε ≫ (adj.homEquiv _ _).symm g) := by
    rw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  rw [h₁, h₂, (adj.homEquiv _ _).apply_eq_iff_eq]
  exact Iff.of_eq (congrArg (fun t => f.app (op ⦋0⦌) ≫ Q.ε = t ≫ (adj.homEquiv _ _).symm g) hε)

/-- **Existence of lifts along a right adjoint**: the adjoint of a lift of the adjoint. -/
lemma exists_isLiftAlong {F : C ⥤ C'} [F.Additive] (adj : F ⊣ G)
    (P : SimplicialProjectiveResolution X) (hP : ∀ n, Projective (F.obj (P.obj _⦋n⦌)))
    (hπ : QuasiIso (P.mapπ F)) (Q : SimplicialProjectiveResolution Y) (g : X ⟶ G.obj Y) :
    ∃ f : P.obj ⟶ Q.obj ⋙ G, IsLiftAlong G P Q g f := by
  obtain ⟨f, hf⟩ := exists_isLift (P.mapOfQuasiIso F hP hπ) Q ((adj.homEquiv _ _).symm g)
  exact ⟨_, (isLift_iff_isLiftAlong adj P hP hπ Q g f).1 hf⟩

end Stacks.SimplicialProjectiveResolution

/-! ### Homology of alternating face map complexes through a functor -/

namespace Stacks

variable {D : Type*} [Category D] [Abelian D] {D' : Type*} [Category D'] [Abelian D']
  {D'' : Type*} [Category D''] [Abelian D'']

/-- For a functor `H : D' ⥤ D` which is additive and preserves homology, a morphism
`α : K ⟶ H(L)` of simplicial objects induces `Hᵢ(s(K)) ⟶ H(Hᵢ(s(L)))` on the homology of the
alternating face map complexes: the map induced on homology by `s(α)`, followed by the
identification `Hᵢ(H(s(L))) ≅ H(Hᵢ(s(L)))`. -/
def alternatingFaceMapHomologyMap {H : D' ⥤ D} [H.Additive] [H.PreservesHomology]
    {K : SimplicialObject D} {L : SimplicialObject D'} (α : K ⟶ L ⋙ H) (i : ℕ) :
    ((alternatingFaceMapComplex D).obj K).homology i ⟶
      H.obj (((alternatingFaceMapComplex D').obj L).homology i) :=
  HomologicalComplex.homologyMap ((alternatingFaceMapComplex D).map α ≫
    (alternatingFaceMapComplexCompIso L H).hom) i ≫
      (((alternatingFaceMapComplex D').obj L).mapHomologyIso H i).hom

variable {H : D' ⥤ D} [H.Additive] [H.PreservesHomology] {K K₀ : SimplicialObject D}
  {L L' : SimplicialObject D'}

/-- `alternatingFaceMapHomologyMap` is compatible with precomposition. -/
lemma alternatingFaceMapHomologyMap_comp_left (β : K₀ ⟶ K) (α : K ⟶ L ⋙ H) (i : ℕ) :
    alternatingFaceMapHomologyMap (β ≫ α) i =
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex D).map β) i ≫
        alternatingFaceMapHomologyMap α i := by
  simp only [alternatingFaceMapHomologyMap, Functor.map_comp, Category.assoc,
    HomologicalComplex.homologyMap_comp]

/-- `alternatingFaceMapHomologyMap` is compatible with postcomposition by the image under `H` of
a morphism. -/
lemma alternatingFaceMapHomologyMap_comp_whiskerRight (α : K ⟶ L ⋙ H) (γ : L ⟶ L') (i : ℕ) :
    alternatingFaceMapHomologyMap (α ≫ Functor.whiskerRight γ H) i =
      alternatingFaceMapHomologyMap α i ≫
        H.map (HomologicalComplex.homologyMap ((alternatingFaceMapComplex D').map γ) i) := by
  have h : (alternatingFaceMapComplex D).map (Functor.whiskerRight γ H) ≫
      (alternatingFaceMapComplexCompIso L' H).hom = (alternatingFaceMapComplexCompIso L H).hom ≫
        (H.mapHomologicalComplex _).map ((alternatingFaceMapComplex D').map γ) := by
    ext n
    simp
  simp only [alternatingFaceMapHomologyMap, Functor.map_comp, Category.assoc, h,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_map_comp_mapHomologyIso_hom]

/-- `alternatingFaceMapHomologyMap` is compatible with postcomposition by the whiskering of a
natural transformation `τ : H ⟶ H'`. -/
lemma alternatingFaceMapHomologyMap_comp_whiskerLeft {H' : D' ⥤ D} [H'.Additive]
    [H'.PreservesHomology] (α : K ⟶ L ⋙ H) (τ : H ⟶ H') (i : ℕ) :
    alternatingFaceMapHomologyMap (α ≫ Functor.whiskerLeft L τ) i =
      alternatingFaceMapHomologyMap α i ≫ τ.app _ := by
  have h : (alternatingFaceMapComplex D).map (Functor.whiskerLeft L τ) ≫
      (alternatingFaceMapComplexCompIso L H').hom = (alternatingFaceMapComplexCompIso L H).hom ≫
        (NatTrans.mapHomologicalComplex τ _).app ((alternatingFaceMapComplex D').obj L) := by
    ext n
    simp
  simp only [alternatingFaceMapHomologyMap, Functor.map_comp, Category.assoc, h,
    HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_app_comp_mapHomologyIso_hom]

/-- `alternatingFaceMapHomologyMap` is compatible with composition of functors. -/
lemma alternatingFaceMapHomologyMap_comp {H₂ : D'' ⥤ D'} [H₂.Additive] [H₂.PreservesHomology]
    {M : SimplicialObject D''} (α : K ⟶ L ⋙ H) (β : L ⟶ M ⋙ H₂) (i : ℕ) :
    alternatingFaceMapHomologyMap (H := H₂ ⋙ H) (α ≫ Functor.whiskerRight β H) i =
      alternatingFaceMapHomologyMap α i ≫ H.map (alternatingFaceMapHomologyMap β i) := by
  have h : (alternatingFaceMapComplex D).map (Functor.whiskerRight β H) ≫
      (alternatingFaceMapComplexCompIso M (H₂ ⋙ H)).hom =
        (alternatingFaceMapComplexCompIso L H).hom ≫ (H.mapHomologicalComplex _).map
          ((alternatingFaceMapComplex D').map β ≫ (alternatingFaceMapComplexCompIso M H₂).hom) := by
    ext n
    simp
  simp only [alternatingFaceMapHomologyMap, Functor.map_comp, Category.assoc, h,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.mapHomologyIso_comp]
  simp only [HomologicalComplex.homologyMap_map_comp_mapHomologyIso_hom_assoc]

/-- For the identity functor, `alternatingFaceMapHomologyMap` is the map induced on homology. -/
lemma alternatingFaceMapHomologyMap_id {K' : SimplicialObject D} (α : K ⟶ K') (i : ℕ) :
    alternatingFaceMapHomologyMap (H := 𝟭 D) α i =
      HomologicalComplex.homologyMap ((alternatingFaceMapComplex D).map α) i := by
  have h : (alternatingFaceMapComplex D).map α ≫ (alternatingFaceMapComplexCompIso K' (𝟭 D)).hom =
      (alternatingFaceMapComplex D).map α := by
    ext n
    simp
  simp only [alternatingFaceMapHomologyMap, h, HomologicalComplex.mapHomologyIso_id,
    Category.comp_id]

/-- **The adjoint of `alternatingFaceMapHomologyMap`.** For an adjunction `F ⊣ G` of additive
functors preserving homology and `α : K ⟶ G(L)`, the morphism `F(Hᵢ(s(K))) ⟶ Hᵢ(s(L))` adjoint to
`Hᵢ(s(K)) ⟶ G(Hᵢ(s(L)))` is the map induced on homology by the adjoint `F(K) ⟶ L` of `α`, under
the identification `F(Hᵢ(s(K))) ≅ Hᵢ(s(F(K)))`. -/
lemma homEquiv_symm_alternatingFaceMapHomologyMap {F : D ⥤ D'} {G : D' ⥤ D} [F.Additive]
    [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (adj : F ⊣ G) (α : K ⟶ L ⋙ G)
    (i : ℕ) :
    (adj.homEquiv _ _).symm (alternatingFaceMapHomologyMap α i) =
      (((alternatingFaceMapComplex D).obj K).mapHomologyIso F i).inv ≫
        HomologicalComplex.homologyMap ((alternatingFaceMapComplexCompIso K F).inv ≫
          (alternatingFaceMapComplex D').map
            (((adj.whiskerRight SimplexCategoryᵒᵖ).homEquiv K L).symm α)) i := by
  have hc : (((G.mapHomologicalComplex _).obj ((alternatingFaceMapComplex D').obj L)).mapHomologyIso
      F i).hom ≫ F.map (((alternatingFaceMapComplex D').obj L).mapHomologyIso G i).hom ≫
        adj.counit.app _ = HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex adj.counit _).app ((alternatingFaceMapComplex D').obj L))
            i := by
    rw [← Category.assoc, ← HomologicalComplex.mapHomologyIso_comp,
      ← HomologicalComplex.homologyMap_app_comp_mapHomologyIso_hom,
      HomologicalComplex.mapHomologyIso_id, Category.comp_id]
  rw [Iso.eq_inv_comp, Adjunction.homEquiv_counit, alternatingFaceMapHomologyMap, F.map_comp]
  simp only [Category.assoc]
  rw [← HomologicalComplex.homologyMap_map_comp_mapHomologyIso_hom_assoc, hc,
    ← HomologicalComplex.homologyMap_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    alternatingFaceMapComplex_map_f, alternatingFaceMapComplexCompIso_hom_f,
    alternatingFaceMapComplexCompIso_inv_f, NatTrans.mapHomologicalComplex_app_f,
    Category.comp_id, Category.id_comp, Adjunction.homEquiv_counit, NatTrans.comp_app,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app,
    Adjunction.whiskerRight_counit_app_app]
  rfl

/-- If the adjoint `F(K) ⟶ L` of `α : K ⟶ G(L)` is an isomorphism, so is the adjoint of
`alternatingFaceMapHomologyMap α i`. -/
lemma isIso_homEquiv_symm_alternatingFaceMapHomologyMap {F : D ⥤ D'} {G : D' ⥤ D} [F.Additive]
    [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (adj : F ⊣ G) (α : K ⟶ L ⋙ G)
    (hα : IsIso (((adj.whiskerRight SimplexCategoryᵒᵖ).homEquiv K L).symm α)) (i : ℕ) :
    IsIso ((adj.homEquiv _ _).symm (alternatingFaceMapHomologyMap α i)) := by
  rw [homEquiv_symm_alternatingFaceMapHomologyMap]
  infer_instance

end Stacks

/-! ### Change of rings for arrows of modules -/

namespace Stacks

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Restriction of scalars along a ring map `f : R →+* S`, applied to arrows of modules. -/
abbrev restrictScalarsArrow (f : R →+* S) :
    ComposableArrows (ModuleCat.{u} S) 1 ⥤ ComposableArrows (ModuleCat.{u} R) 1 :=
  (Functor.whiskeringRight (Fin 2) _ _).obj (ModuleCat.restrictScalars.{u} f)

/-- Extension of scalars along a ring map `f : R →+* S`, applied to arrows of modules. -/
abbrev extendScalarsArrow (f : R →+* S) :
    ComposableArrows (ModuleCat.{u} R) 1 ⥤ ComposableArrows (ModuleCat.{u} S) 1 :=
  (Functor.whiskeringRight (Fin 2) _ _).obj (ModuleCat.extendScalars.{u, u, u} f)

/-- Extension of scalars of arrows is left adjoint to restriction of scalars. -/
def extendRestrictScalarsArrowAdj (f : R →+* S) :
    extendScalarsArrow f ⊣ restrictScalarsArrow f :=
  (ModuleCat.extendRestrictScalarsAdj f).whiskerRight (Fin 2)

/-- Restriction of scalars of arrows preserves finite limits. -/
instance preservesFiniteLimits_restrictScalarsArrow (f : R →+* S) :
    PreservesFiniteLimits (restrictScalarsArrow f) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Restriction of scalars of arrows preserves finite colimits. -/
instance preservesFiniteColimits_restrictScalarsArrow (f : R →+* S) :
    PreservesFiniteColimits (restrictScalarsArrow f) :=
  ⟨fun _ _ _ => inferInstance⟩

/-- Extension of scalars of arrows preserves projective objects: it is left adjoint to
restriction of scalars, which preserves epimorphisms. -/
instance preservesProjectiveObjects_extendScalarsArrow (f : R →+* S) :
    (extendScalarsArrow f).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (extendRestrictScalarsArrowAdj f)

/-- Extension of scalars of arrows along a flat ring map is exact. -/
lemma extendScalarsArrow_preservesHomology (f : R →+* S) (hf : f.Flat) :
    (extendScalarsArrow f).PreservesHomology := by
  have := extendScalars_preservesFiniteLimits_of_flat'.{u, u} f hf
  have : PreservesColimitsOfSize.{0, 0} (ModuleCat.extendScalars.{u, u, u} f) :=
    (ModuleCat.extendRestrictScalarsAdj f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits (ModuleCat.extendScalars.{u, u, u} f) :=
    PreservesColimitsOfSize.preservesFiniteColimits _
  have : PreservesFiniteLimits (extendScalarsArrow f) := ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteColimits (extendScalarsArrow f) := ⟨fun _ _ _ => inferInstance⟩
  infer_instance

/-- Restriction of scalars of arrows along a ring map equal to the identity is the identity. -/
def restrictScalarsArrowId' (f : R →+* R) (hf : f = RingHom.id R) :
    restrictScalarsArrow f ≅ 𝟭 _ :=
  (Functor.whiskeringRight (Fin 2) _ _).mapIso (ModuleCat.restrictScalarsId' f hf) ≪≫
    Functor.whiskeringRightObjIdIso

/-- Restriction of scalars of arrows along a composite of ring maps is the composite of the
restrictions. -/
def restrictScalarsArrowComp' (f : R →+* S) (g : S →+* T) (gf : R →+* T)
    (hgf : gf = g.comp f) :
    restrictScalarsArrow gf ≅ restrictScalarsArrow g ⋙ restrictScalarsArrow f :=
  (Functor.whiskeringRight (Fin 2) _ _).mapIso (ModuleCat.restrictScalarsComp' f g gf hgf) ≪≫
    (Functor.whiskeringRightObjCompIso _ _).symm

namespace SimplicialProjectiveResolution

/-- Extension of scalars of arrows along a flat ring map carries the augmentation of a simplicial
projective resolution to a quasi-isomorphism. -/
instance quasiIso_mapπ_extendScalarsArrow (f : R →+* S) [Fact f.Flat]
    {X : ComposableArrows (ModuleCat.{u} R) 1} (P : SimplicialProjectiveResolution X) :
    QuasiIso (P.mapπ (extendScalarsArrow f)) :=
  haveI := extendScalarsArrow_preservesHomology f Fact.out
  inferInstance

/-- The base change `S ⊗_R P` of a simplicial projective resolution `P` of an arrow of
`R`-modules along a flat ring map `f : R →+* S`: a simplicial projective resolution of the base
change of the arrow. -/
abbrev extendScalarsArrow (f : R →+* S) (hf : f.Flat) {X : ComposableArrows (ModuleCat.{u} R) 1}
    (P : SimplicialProjectiveResolution X) :
    SimplicialProjectiveResolution ((Stacks.extendScalarsArrow f).obj X) :=
  haveI : Fact f.Flat := ⟨hf⟩
  P.mapOfQuasiIso (Stacks.extendScalarsArrow f)
    (fun _ => (Stacks.extendScalarsArrow f).projective_obj _) inferInstance

end SimplicialProjectiveResolution

end Stacks

namespace Stacks.Modules

/-- A `φ`-semilinear map whose linearization `S ⊗_R M → N` is an isomorphism exhibits its target
as the base change of its source along `φ`. -/
theorem isBaseChangeAlong_of_isIso {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)
    {M : ModuleCat.{u} R} {N : ModuleCat.{u} S} (g : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    [IsIso (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm g)] :
    IsBaseChangeAlong φ ((ModuleCat.semilinearMapAddEquiv φ M N).symm g) := by
  unfold IsBaseChangeAlong
  let := φ.toAlgebra
  let := Module.compHom N φ
  let : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let v := ((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).symm g
  let e₀ : (ModuleCat.extendScalars φ).obj M ≃ₗ[S] S ⊗[R] M := LinearEquiv.refl S _
  refine IsBaseChange.of_equiv (e₀.symm.trans (asIso v).toLinearEquiv) fun x => ?_
  exact (ModuleCat.extendRestrictScalarsAdj_homEquiv_apply v x).symm.trans
    (congrArg (fun t => t.hom x)
      (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M N).apply_symm_apply g))

end Stacks.Modules

/-! ### Semilinear functors on arrows of modules -/

namespace Stacks

/-- A **semilinear functor on arrows of modules**: for every commutative ring `A` a functor
`Φ_A` from arrows of `A`-modules to `A`-modules, and for every ring map `φ : A ⟶ B` an `A`-linear
natural transformation `σ_φ : Φ_A(φ^* Y) ⟶ φ^* Φ_B(Y)`, where `φ^*` is restriction of scalars,
which is the identity for `φ = 𝟙` and is transitive for composites. Examples are the exterior and
tensor squares of the source, of the target or of the cokernel of an arrow. -/
structure SemilinearArrowFunctor where
  /-- The functor on arrows of `A`-modules. -/
  obj (A : CommRingCat.{u}) : ComposableArrows (ModuleCat.{u} A) 1 ⥤ ModuleCat.{u} A
  /-- The semilinear structure `σ_φ : Φ_A(φ^* Y) ⟶ φ^* Φ_B(Y)`. -/
  map {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    restrictScalarsArrow φ.hom ⋙ obj A ⟶ obj B ⋙ ModuleCat.restrictScalars.{u} φ.hom
  /-- The semilinear structure of the identity is the identity. -/
  map_id (A : CommRingCat.{u}) (Y : ComposableArrows (ModuleCat.{u} A) 1) :
    (obj A).map ((restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.app Y) ≫
        (map (𝟙 A)).app Y =
      (ModuleCat.restrictScalarsId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.app ((obj A).obj Y)
  /-- The semilinear structure of a composite is the composite of the semilinear
  structures. -/
  map_comp {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    (Z : ComposableArrows (ModuleCat.{u} C) 1) :
    (obj A).map
        ((restrictScalarsArrowComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv.app Z) ≫
        (map (φ ≫ ψ)).app Z =
      (map φ).app ((restrictScalarsArrow ψ.hom).obj Z) ≫
        (ModuleCat.restrictScalars φ.hom).map ((map ψ).app Z) ≫
          (ModuleCat.restrictScalarsComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv.app
            ((obj C).obj Z)

namespace SemilinearArrowFunctor

/-- A morphism of semilinear functors on arrows: natural transformations `Φ_A ⟶ Ψ_A` compatible
with the semilinear structures. -/
@[ext]
structure Hom (Φ Ψ : SemilinearArrowFunctor.{u}) where
  /-- The natural transformation over the ring `A`. -/
  app (A : CommRingCat.{u}) : Φ.obj A ⟶ Ψ.obj A
  /-- Compatibility with the semilinear structures. -/
  comm {A B : CommRingCat.{u}} (φ : A ⟶ B) :
    Functor.whiskerLeft (restrictScalarsArrow φ.hom) (app A) ≫ Ψ.map φ =
      Φ.map φ ≫ Functor.whiskerRight (app B) (ModuleCat.restrictScalars φ.hom)

/-- Semilinear functors on arrows form a category. -/
instance category : Category SemilinearArrowFunctor.{u} where
  Hom := Hom
  id Φ := ⟨fun A => 𝟙 _, fun φ => by simp⟩
  comp α β := ⟨fun A => α.app A ≫ β.app A, fun φ => by
    rw [Functor.whiskerLeft_comp, Category.assoc, β.comm, ← Category.assoc, α.comm,
      Category.assoc, Functor.whiskerRight_comp]⟩

variable {Φ Ψ Θ : SemilinearArrowFunctor.{u}}

/-- Morphisms of semilinear functors on arrows are determined by their components. -/
@[ext]
lemma hom_ext {α β : Φ ⟶ Ψ} (h : ∀ A, α.app A = β.app A) : α = β :=
  Hom.ext (funext h)

/-- The components of the identity. -/
@[simp]
lemma id_app (A : CommRingCat.{u}) : (𝟙 Φ : Φ ⟶ Φ).app A = 𝟙 _ :=
  rfl

/-- The components of a composite. -/
@[simp]
lemma comp_app (α : Φ ⟶ Ψ) (β : Ψ ⟶ Θ) (A : CommRingCat.{u}) :
    (α ≫ β).app A = α.app A ≫ β.app A :=
  rfl

variable (Φ) {A B C : CommRingCat.{u}} (φ : A ⟶ B)

/-- The `A`-linear base change morphism `Φ_A(P) ⟶ φ^* Φ_B(B ⊗_A P)`: `Φ_A` applied to the unit
`P ⟶ φ^*(B ⊗_A P)`, followed by the semilinear structure. -/
def baseChange :
    Φ.obj A ⟶ extendScalarsArrow φ.hom ⋙ Φ.obj B ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.whiskerRight (extendRestrictScalarsArrowAdj φ.hom).unit (Φ.obj A) ≫
    Functor.whiskerLeft (extendScalarsArrow φ.hom) (Φ.map φ)

/-- `Φ` *commutes with flat base change on projective arrows*: for every flat ring map
`φ : A ⟶ B` and every projective arrow `P` of `A`-modules, the `B`-linear map
`B ⊗_A Φ_A(P) ⟶ Φ_B(B ⊗_A P)` adjoint to `Φ.baseChange φ` is bijective. -/
def HasFlatBaseChange : Prop :=
  ∀ ⦃A B : CommRingCat.{u}⦄ (φ : A ⟶ B), φ.hom.Flat →
    ∀ (P : ComposableArrows (ModuleCat.{u} A) 1), Projective P →
      IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
        ((Φ.baseChange φ).app P))

/-- The morphism of simplicial `A`-modules `Φ_A(K) ⟶ φ^* Φ_B(L)` induced by a semilinear morphism
`h : K ⟶ φ^* L` of simplicial arrows: `Φ_A(h)` followed by the semilinear structure. -/
def simplicialMap {K : SimplicialObject (ComposableArrows (ModuleCat.{u} A) 1)}
    {L : SimplicialObject (ComposableArrows (ModuleCat.{u} B) 1)}
    (h : K ⟶ L ⋙ restrictScalarsArrow φ.hom) :
    K ⋙ Φ.obj A ⟶ (L ⋙ Φ.obj B) ⋙ ModuleCat.restrictScalars φ.hom :=
  Functor.whiskerRight h (Φ.obj A) ≫ Functor.whiskerLeft L (Φ.map φ)

variable {K K₀ : SimplicialObject (ComposableArrows (ModuleCat.{u} A) 1)}
  {L L' : SimplicialObject (ComposableArrows (ModuleCat.{u} B) 1)}
  {M : SimplicialObject (ComposableArrows (ModuleCat.{u} C) 1)}

/-- `simplicialMap` is compatible with precomposition. -/
lemma simplicialMap_comp_left (k : K₀ ⟶ K) (h : K ⟶ L ⋙ restrictScalarsArrow φ.hom) :
    Φ.simplicialMap φ (k ≫ h) = Functor.whiskerRight k (Φ.obj A) ≫ Φ.simplicialMap φ h := by
  simp only [simplicialMap, Functor.whiskerRight_comp, Category.assoc]

/-- `simplicialMap` is compatible with postcomposition. -/
lemma simplicialMap_comp_whiskerRight (h : K ⟶ L ⋙ restrictScalarsArrow φ.hom) (g : L ⟶ L') :
    Φ.simplicialMap φ (h ≫ Functor.whiskerRight g (restrictScalarsArrow φ.hom)) =
      Φ.simplicialMap φ h ≫ Functor.whiskerRight (Functor.whiskerRight g (Φ.obj B))
        (ModuleCat.restrictScalars φ.hom) := by
  refine NatTrans.ext (funext fun n => ?_)
  simp only [simplicialMap, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  exact congrArg ((Φ.obj A).map (h.app n) ≫ ·) ((Φ.map φ).naturality (g.app n))

/-- `simplicialMap` along the identity, for a morphism followed by the identification
`L ≅ (𝟙 A)^* L`. -/
lemma simplicialMap_id {K L : SimplicialObject (ComposableArrows (ModuleCat.{u} A) 1)}
    (k : K ⟶ L) :
    Φ.simplicialMap (𝟙 A)
        (k ≫ Functor.whiskerLeft L (restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv) =
      Functor.whiskerRight k (Φ.obj A) ≫ Functor.whiskerLeft (L ⋙ Φ.obj A)
        (ModuleCat.restrictScalarsId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv := by
  refine NatTrans.ext (funext fun n => ?_)
  simp only [simplicialMap, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  exact congrArg ((Φ.obj A).map (k.app n) ≫ ·) (Φ.map_id A (L.obj n))

/-- `simplicialMap` along a composite of ring maps, for a composite of semilinear morphisms. -/
lemma simplicialMap_comp (ψ : B ⟶ C) (h₁ : K ⟶ L ⋙ restrictScalarsArrow φ.hom)
    (h₂ : L ⟶ M ⋙ restrictScalarsArrow ψ.hom) :
    Φ.simplicialMap (φ ≫ ψ) (h₁ ≫ Functor.whiskerRight h₂ (restrictScalarsArrow φ.hom) ≫
      Functor.whiskerLeft M
        (restrictScalarsArrowComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv) =
      Φ.simplicialMap φ h₁ ≫
        Functor.whiskerRight (Φ.simplicialMap ψ h₂) (ModuleCat.restrictScalars φ.hom) ≫
          Functor.whiskerLeft (M ⋙ Φ.obj C)
            (ModuleCat.restrictScalarsComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv := by
  refine NatTrans.ext (funext fun n => ?_)
  simp only [simplicialMap, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [Φ.map_comp φ ψ (M.obj n)]
  exact congrArg ((Φ.obj A).map (h₁.app n) ≫ ·) ((Φ.map φ).naturality_assoc (h₂.app n) _)

/-- `simplicialMap` is natural in the semilinear functor. -/
lemma simplicialMap_naturality (α : Φ ⟶ Ψ) (h : K ⟶ L ⋙ restrictScalarsArrow φ.hom) :
    Functor.whiskerLeft K (α.app A) ≫ Ψ.simplicialMap φ h =
      Φ.simplicialMap φ h ≫ Functor.whiskerRight (Functor.whiskerLeft L (α.app B))
        (ModuleCat.restrictScalars φ.hom) := by
  refine NatTrans.ext (funext fun n => ?_)
  have := NatTrans.congr_app (α.comm φ) (L.obj n)
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.comp_obj] at this
  simp only [simplicialMap, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [← this]
  exact ((α.app A).naturality_assoc (h.app n) _).symm

end SemilinearArrowFunctor

end Stacks

/-! ### Derived semilinear maps -/

/-- The components of the adjoint, for the adjunction of whiskered functors, of a natural
transformation `K ⟶ L ⋙ G` are the adjoints of its components. -/
lemma CategoryTheory.Adjunction.whiskerRight_homEquiv_symm_app {C D E : Type*} [Category C]
    [Category D] [Category E] {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) {K : C ⥤ D} {L : C ⥤ E}
    (β : K ⟶ L ⋙ G) (c : C) :
    (((adj.whiskerRight C).homEquiv K L).symm β).app c = (adj.homEquiv _ _).symm (β.app c) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  simp

namespace Stacks.SimplicialProjectiveResolution

variable {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Preadditive D]
  [CategoryWithHomology D] {X Y : C}

/-- The morphism `Hᵢ(s(F(P))) ⟶ Hᵢ(s(F'(P)))` of derived objects induced by a natural
transformation `τ : F ⟶ F'`. -/
def derivedHomologyMap {F F' : C ⥤ D} (τ : F ⟶ F') (P : SimplicialProjectiveResolution X)
    (i : ℕ) : P.derivedHomology F i ⟶ P.derivedHomology F' i :=
  HomologicalComplex.homologyMap ((alternatingFaceMapComplex D).map (Functor.whiskerLeft P.obj τ))
    i

/-- An isomorphism induces isomorphisms of derived objects. -/
instance isIso_derivedMap (F : C ⥤ D) (g : X ⟶ Y) [IsIso g] (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (i : ℕ) : IsIso (derivedMap F g P Q i) :=
  ⟨⟨derivedMap F (inv g) Q P i, by simp, by simp⟩⟩

end Stacks.SimplicialProjectiveResolution

namespace Stacks.SemilinearArrowFunctor

open SimplicialProjectiveResolution

variable (Φ : SemilinearArrowFunctor.{u}) {A B C : CommRingCat.{u}} (φ : A ⟶ B)
  (hφ : φ.hom.Flat) {X : ComposableArrows (ModuleCat.{u} A) 1}
  {Y : ComposableArrows (ModuleCat.{u} B) 1}

include hφ in
/-- Semilinear lifts exist along flat ring maps: they are the adjoints of the lifts to the base
change of the resolution. -/
lemma exists_isLiftAlong (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y) :
    ∃ h : P.obj ⟶ Q.obj ⋙ restrictScalarsArrow φ.hom,
      P.IsLiftAlong (restrictScalarsArrow φ.hom) Q f h :=
  have : Fact φ.hom.Flat := ⟨hφ⟩
  SimplicialProjectiveResolution.exists_isLiftAlong (extendRestrictScalarsArrowAdj φ.hom) P
    (fun _ => (extendScalarsArrow φ.hom).projective_obj _) inferInstance Q f

/-- The base change morphism `Hⱼ(Φ_A(P)) ⟶ φ^* Hⱼ(Φ_B(B ⊗_A P))` of derived objects, induced by
the base change morphism `Φ.baseChange φ` in each degree. -/
def derivedBaseChange (P : SimplicialProjectiveResolution X) (j : ℕ) :
    P.derivedHomology (Φ.obj A) j ⟶ (ModuleCat.restrictScalars φ.hom).obj
      ((P.extendScalarsArrow φ.hom hφ).derivedHomology (Φ.obj B) j) :=
  alternatingFaceMapHomologyMap (Φ.simplicialMap φ (K := P.obj)
    (L := P.obj ⋙ extendScalarsArrow φ.hom)
    (((extendRestrictScalarsArrowAdj φ.hom).whiskerRight SimplexCategoryᵒᵖ).unit.app P.obj)) j

/-- **The derived semilinear map.** For a flat ring map `φ : A ⟶ B` and a morphism
`f : X ⟶ φ^* Y` from an arrow of `A`-modules to the restriction of an arrow of `B`-modules, the
`A`-linear map `Hⱼ(Φ_A(P)) ⟶ φ^* Hⱼ(Φ_B(Q))` computed by simplicial projective resolutions `P` of
`X` and `Q` of `Y`: the base change morphism followed by the map induced by the adjoint
`B ⊗_A X ⟶ Y` of `f`. By `derivedMap_eq` it is computed by any semilinear lift of `f`. -/
def derivedMap (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y) (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    P.derivedHomology (Φ.obj A) j ⟶
      (ModuleCat.restrictScalars φ.hom).obj (Q.derivedHomology (Φ.obj B) j) :=
  Φ.derivedBaseChange φ hφ P j ≫ (ModuleCat.restrictScalars φ.hom).map
    (SimplicialProjectiveResolution.derivedMap (Φ.obj B)
      (((extendRestrictScalarsArrowAdj φ.hom).homEquiv _ _).symm f)
      (P.extendScalarsArrow φ.hom hφ) Q j)

/-- **The derived semilinear map is computed by any semilinear lift.** -/
theorem derivedMap_eq {f : X ⟶ (restrictScalarsArrow φ.hom).obj Y}
    {P : SimplicialProjectiveResolution X} {Q : SimplicialProjectiveResolution Y}
    {h : P.obj ⟶ Q.obj ⋙ restrictScalarsArrow φ.hom}
    (hh : P.IsLiftAlong (restrictScalarsArrow φ.hom) Q f h) (j : ℕ) :
    Φ.derivedMap φ hφ f P Q j = alternatingFaceMapHomologyMap (Φ.simplicialMap φ h) j := by
  have : Fact φ.hom.Flat := ⟨hφ⟩
  obtain ⟨g, rfl⟩ : ∃ g, ((extendRestrictScalarsArrowAdj φ.hom).whiskerRight
      SimplexCategoryᵒᵖ).homEquiv P.obj Q.obj g = h :=
    ⟨_, Equiv.apply_symm_apply _ h⟩
  have hg : IsLift (P.extendScalarsArrow φ.hom hφ) Q
      (((extendRestrictScalarsArrowAdj φ.hom).homEquiv _ _).symm f) g :=
    (isLift_iff_isLiftAlong (extendRestrictScalarsArrowAdj φ.hom) P
      (fun _ => (extendScalarsArrow φ.hom).projective_obj _) inferInstance Q f g).2 hh
  rw [Adjunction.homEquiv_unit, Functor.whiskeringRight_obj_map,
    Φ.simplicialMap_comp_whiskerRight, alternatingFaceMapHomologyMap_comp_whiskerRight,
    derivedMap, hg.derivedMap_eq]
  rfl

/-- **The derived semilinear map**, as a `φ`-semilinear map `Hⱼ(Φ_A(P)) →ₛₗ[φ] Hⱼ(Φ_B(Q))`. -/
def derivedSemilinearMap (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    ↥(P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) →ₛₗ[φ.hom]
      ↥(Q.derivedHomology (D := ModuleCat.{u} B) (Φ.obj B) j) :=
  (ModuleCat.semilinearMapAddEquiv φ.hom _ _).symm (Φ.derivedMap φ hφ f P Q j)

/-- The derived semilinear map is the derived map on elements. -/
lemma derivedSemilinearMap_apply (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ)
    (x : P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) :
    Φ.derivedSemilinearMap φ hφ f P Q j x = (Φ.derivedMap φ hφ f P Q j).hom x :=
  rfl

/-- The derived semilinear maps are compatible with the derived maps of the source. -/
@[reassoc]
theorem derivedMap_comp_derivedMap {X₀ : ComposableArrows (ModuleCat.{u} A) 1} (g₀ : X₀ ⟶ X)
    (P₀ : SimplicialProjectiveResolution X₀) (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    SimplicialProjectiveResolution.derivedMap (Φ.obj A) g₀ P₀ P j ≫ Φ.derivedMap φ hφ f P Q j =
      Φ.derivedMap φ hφ (g₀ ≫ f) P₀ Q j := by
  obtain ⟨k, hk⟩ := exists_isLift P₀ P g₀
  obtain ⟨h, hh⟩ := exists_isLiftAlong φ hφ P Q f
  rw [hk.derivedMap_eq, Φ.derivedMap_eq φ hφ hh, Φ.derivedMap_eq φ hφ (hk.comp_isLiftAlong hh),
    Φ.simplicialMap_comp_left, alternatingFaceMapHomologyMap_comp_left]

/-- The derived semilinear maps are compatible with the derived maps of the target. -/
@[reassoc]
theorem derivedMap_comp_map_derivedMap (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    {Y' : ComposableArrows (ModuleCat.{u} B) 1} (g₁ : Y ⟶ Y')
    (Q' : SimplicialProjectiveResolution Y') (j : ℕ) :
    Φ.derivedMap φ hφ f P Q j ≫ (ModuleCat.restrictScalars φ.hom).map
        (SimplicialProjectiveResolution.derivedMap (Φ.obj B) g₁ Q Q' j) =
      Φ.derivedMap φ hφ (f ≫ (restrictScalarsArrow φ.hom).map g₁) P Q' j := by
  obtain ⟨k, hk⟩ := exists_isLift Q Q' g₁
  obtain ⟨h, hh⟩ := exists_isLiftAlong φ hφ P Q f
  rw [hk.derivedMap_eq, Φ.derivedMap_eq φ hφ hh, Φ.derivedMap_eq φ hφ (hh.comp_whiskerRight hk),
    Φ.simplicialMap_comp_whiskerRight, alternatingFaceMapHomologyMap_comp_whiskerRight]

/-- The derived semilinear maps are compatible with the comparison isomorphisms between
resolutions of the source. -/
@[reassoc (attr := simp)]
theorem derivedIso_hom_comp_derivedMap (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P P' : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    (derivedIso (Φ.obj A) P P' j).hom ≫ Φ.derivedMap φ hφ f P' Q j =
      Φ.derivedMap φ hφ f P Q j := by
  rw [derivedIso_hom, derivedMap_comp_derivedMap, Category.id_comp]

/-- The derived semilinear maps are compatible with the comparison isomorphisms between
resolutions of the target. -/
@[reassoc (attr := simp)]
theorem derivedMap_comp_map_derivedIso_hom (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (P : SimplicialProjectiveResolution X) (Q Q' : SimplicialProjectiveResolution Y) (j : ℕ) :
    Φ.derivedMap φ hφ f P Q j ≫
        (ModuleCat.restrictScalars φ.hom).map (derivedIso (Φ.obj B) Q Q' j).hom =
      Φ.derivedMap φ hφ f P Q' j := by
  rw [derivedIso_hom, derivedMap_comp_map_derivedMap, CategoryTheory.Functor.map_id,
    Category.comp_id]

/-- **Naturality in the semilinear functor.** A morphism `α : Φ ⟶ Ψ` of semilinear functors on
arrows commutes with the derived semilinear maps. -/
@[reassoc]
theorem derivedHomologyMap_comp_derivedMap {Ψ : SemilinearArrowFunctor.{u}} (α : Φ ⟶ Ψ)
    (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y) (P : SimplicialProjectiveResolution X)
    (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    derivedHomologyMap (α.app A) P j ≫ Ψ.derivedMap φ hφ f P Q j =
      Φ.derivedMap φ hφ f P Q j ≫
        (ModuleCat.restrictScalars φ.hom).map (derivedHomologyMap (α.app B) Q j) := by
  obtain ⟨h, hh⟩ := exists_isLiftAlong φ hφ P Q f
  rw [Φ.derivedMap_eq φ hφ hh, Ψ.derivedMap_eq φ hφ hh, derivedHomologyMap, derivedHomologyMap,
    ← alternatingFaceMapHomologyMap_comp_left, ← alternatingFaceMapHomologyMap_comp_whiskerRight,
    simplicialMap_naturality]

/-- **Transitivity of the derived semilinear maps.** For flat ring maps `φ : A ⟶ B`,
`ψ : B ⟶ C` and `χ = φ ≫ ψ`, the derived semilinear map of the composite
`X ⟶ φ^* Y ⟶ φ^* ψ^* Z ≅ χ^* Z` is the composite of the derived semilinear maps, under the
identification `χ^* ≅ φ^* ψ^*`. The composite ring map `χ` is only required to be equal to
`φ ≫ ψ`. -/
theorem derivedMap_comp_restrictScalarsComp'_hom (ψ : B ⟶ C) (χ : A ⟶ C) (hχ : χ = φ ≫ ψ)
    (hψ : ψ.hom.Flat) (hχf : χ.hom.Flat) {Z : ComposableArrows (ModuleCat.{u} C) 1}
    (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y) (g : Y ⟶ (restrictScalarsArrow ψ.hom).obj Z)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (R : SimplicialProjectiveResolution Z) (j : ℕ) :
    Φ.derivedMap χ hχf (f ≫ (restrictScalarsArrow φ.hom).map g ≫
        (restrictScalarsArrowComp' φ.hom ψ.hom χ.hom (congrArg CommRingCat.Hom.hom hχ)).inv.app Z)
          P R j ≫
        (ModuleCat.restrictScalarsComp' φ.hom ψ.hom χ.hom
          (congrArg CommRingCat.Hom.hom hχ)).hom.app _ =
      Φ.derivedMap φ hφ f P Q j ≫
        (ModuleCat.restrictScalars φ.hom).map (Φ.derivedMap ψ hψ g Q R j) := by
  subst hχ
  obtain ⟨h₁, hh₁⟩ := exists_isLiftAlong φ hφ P Q f
  obtain ⟨h₂, hh₂⟩ := exists_isLiftAlong ψ hψ Q R g
  have hh := (hh₁.comp hh₂).comp_whiskerLeft
    (restrictScalarsArrowComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv
  simp only [Category.assoc] at hh
  have e₁ := alternatingFaceMapHomologyMap_comp_whiskerLeft
    (H := ModuleCat.restrictScalars ψ.hom ⋙ ModuleCat.restrictScalars φ.hom)
    (H' := ModuleCat.restrictScalars (CommRingCat.Hom.hom (φ ≫ ψ))) (L := R.obj ⋙ Φ.obj C)
    (Φ.simplicialMap φ h₁ ≫
      Functor.whiskerRight (Φ.simplicialMap ψ h₂) (ModuleCat.restrictScalars φ.hom))
    (ModuleCat.restrictScalarsComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv j
  have key : alternatingFaceMapHomologyMap (Φ.simplicialMap (φ ≫ ψ)
      (h₁ ≫ Functor.whiskerRight h₂ (restrictScalarsArrow φ.hom) ≫ Functor.whiskerLeft R.obj
        (restrictScalarsArrowComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ)) rfl).inv)) j =
      alternatingFaceMapHomologyMap
        (H := ModuleCat.restrictScalars ψ.hom ⋙ ModuleCat.restrictScalars φ.hom)
        (Φ.simplicialMap φ h₁ ≫
          Functor.whiskerRight (Φ.simplicialMap ψ h₂) (ModuleCat.restrictScalars φ.hom)) j ≫
        (ModuleCat.restrictScalarsComp' φ.hom ψ.hom (CommRingCat.Hom.hom (φ ≫ ψ))
          rfl).inv.app _ := by
    rw [Φ.simplicialMap_comp]
    exact (congrArg (fun t => alternatingFaceMapHomologyMap t j)
      (Category.assoc _ _ _).symm).trans e₁
  rw [Φ.derivedMap_eq _ _ hh, Φ.derivedMap_eq _ _ hh₁, Φ.derivedMap_eq _ _ hh₂, key,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id, alternatingFaceMapHomologyMap_comp]

/-- **Transitivity of the derived semilinear maps**, on elements: the derived semilinear map of
the composite `X ⟶ φ^* Y ⟶ φ^* ψ^* Z ≅ χ^* Z` is the composite of the derived semilinear maps. -/
theorem derivedSemilinearMap_comp_apply (ψ : B ⟶ C) (χ : A ⟶ C) (hχ : χ = φ ≫ ψ)
    (hψ : ψ.hom.Flat) (hχf : χ.hom.Flat) {Z : ComposableArrows (ModuleCat.{u} C) 1}
    (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y) (g : Y ⟶ (restrictScalarsArrow ψ.hom).obj Z)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y)
    (R : SimplicialProjectiveResolution Z) (j : ℕ)
    (x : P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) :
    Φ.derivedSemilinearMap χ hχf (f ≫ (restrictScalarsArrow φ.hom).map g ≫
        (restrictScalarsArrowComp' φ.hom ψ.hom χ.hom (congrArg CommRingCat.Hom.hom hχ)).inv.app Z)
          P R j x =
      Φ.derivedSemilinearMap ψ hψ g Q R j (Φ.derivedSemilinearMap φ hφ f P Q j x) :=
  congrArg (fun t => t.hom x)
    (Φ.derivedMap_comp_restrictScalarsComp'_hom φ hφ ψ χ hχ hψ hχf f g P Q R j)

/-- **The derived semilinear map along the identity** is the derived map of the corresponding
morphism of arrows of `A`-modules. -/
theorem derivedMap_id_comp_restrictScalarsId'_hom {Y : ComposableArrows (ModuleCat.{u} A) 1}
    (f : X ⟶ (restrictScalarsArrow (CommRingCat.Hom.hom (𝟙 A))).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    Φ.derivedMap (𝟙 A) (RingHom.Flat.id A) f P Q j ≫
        (ModuleCat.restrictScalarsId' (CommRingCat.Hom.hom (𝟙 A)) rfl).hom.app _ =
      SimplicialProjectiveResolution.derivedMap (Φ.obj A)
        (f ≫ (restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).hom.app Y) P Q j := by
  obtain ⟨k, hk⟩ := exists_isLift P Q
    (f ≫ (restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).hom.app Y)
  have hk' : P.IsLiftAlong (𝟭 _) Q _ k := (isLift_iff _ _).1 hk
  have hh := hk'.comp_whiskerLeft (restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at hh
  have e₁ := alternatingFaceMapHomologyMap_comp_whiskerLeft (H := 𝟭 _)
    (H' := ModuleCat.restrictScalars (CommRingCat.Hom.hom (𝟙 A))) (L := Q.obj ⋙ Φ.obj A)
    (Functor.whiskerRight k (Φ.obj A))
    (ModuleCat.restrictScalarsId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv j
  rw [Φ.derivedMap_eq _ _ hh, Φ.simplicialMap_id, e₁, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id, alternatingFaceMapHomologyMap_id, hk.derivedMap_eq]

/-- **The derived semilinear map along the identity**, on elements. -/
theorem derivedSemilinearMap_id_apply {Y : ComposableArrows (ModuleCat.{u} A) 1}
    (f : X ⟶ (restrictScalarsArrow (CommRingCat.Hom.hom (𝟙 A))).obj Y)
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ)
    (x : P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) :
    Φ.derivedSemilinearMap (𝟙 A) (RingHom.Flat.id A) f P Q j x =
      (SimplicialProjectiveResolution.derivedMap (Φ.obj A)
        (f ≫ (restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).hom.app Y) P Q j).hom x :=
  congrArg (fun t => t.hom x) (Φ.derivedMap_id_comp_restrictScalarsId'_hom f P Q j)

/-- **The derived semilinear map of the identity is the identity.** -/
@[simp]
theorem derivedSemilinearMap_id_apply_self (P : SimplicialProjectiveResolution X) (j : ℕ)
    (x : P.derivedHomology (D := ModuleCat.{u} A) (Φ.obj A) j) :
    Φ.derivedSemilinearMap (𝟙 A) (RingHom.Flat.id A)
      ((restrictScalarsArrowId' (CommRingCat.Hom.hom (𝟙 A)) rfl).inv.app X) P P j x = x := by
  rw [derivedSemilinearMap_id_apply, Iso.inv_hom_id_app,
    SimplicialProjectiveResolution.derivedMap_id]
  rfl

variable {Φ} in
/-- If `Φ` commutes with flat base change on projective arrows, the base change morphism of
derived objects is a base change: its linearization `B ⊗_A Hⱼ(Φ_A(P)) ⟶ Hⱼ(Φ_B(B ⊗_A P))` is
an isomorphism, because `B ⊗_A -` is exact and the terms of `P` are projective arrows. -/
theorem isIso_homEquiv_symm_derivedBaseChange (hΦ : Φ.HasFlatBaseChange)
    (P : SimplicialProjectiveResolution X) (j : ℕ) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
      (Φ.derivedBaseChange φ hφ P j)) := by
  have := extendScalars_preservesHomology_of_flat.{u, u} φ.hom hφ
  refine isIso_homEquiv_symm_alternatingFaceMapHomologyMap _ _ ?_ j
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun n => ?_
  have e : ((((ModuleCat.extendRestrictScalarsAdj φ.hom).whiskerRight SimplexCategoryᵒᵖ).homEquiv
      (P.obj ⋙ Φ.obj A) ((P.extendScalarsArrow φ.hom hφ).obj ⋙ Φ.obj B)).symm
        (Φ.simplicialMap φ (K := P.obj) (L := P.obj ⋙ extendScalarsArrow φ.hom)
          (((extendRestrictScalarsArrowAdj φ.hom).whiskerRight SimplexCategoryᵒᵖ).unit.app
            P.obj))).app n =
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
        ((Φ.baseChange φ).app (P.obj.obj n)) := by
    refine (Adjunction.whiskerRight_homEquiv_symm_app _ _ n).trans (congrArg _ ?_)
    simp [simplicialMap, baseChange, extendRestrictScalarsArrowAdj]
    rfl
  rw [e]
  exact hΦ φ hφ _ (P.projective n.unop.len)

variable {Φ} in
/-- **The derived semilinear maps are base changes.** Let `Φ` commute with flat base change on
projective arrows, let `φ : A ⟶ B` be flat (for instance a localization `A ⟶ A_𝔭`), and let
`f : X ⟶ φ^* Y` have adjoint `B ⊗_A X ⟶ Y` an isomorphism. Then the derived semilinear map
`Hⱼ(Φ_A(P)) →ₛₗ[φ] Hⱼ(Φ_B(Q))` exhibits its target as the base change of its source along `φ`. -/
theorem isBaseChangeAlong_derivedSemilinearMap (hΦ : Φ.HasFlatBaseChange)
    (f : X ⟶ (restrictScalarsArrow φ.hom).obj Y)
    (hf : IsIso (((extendRestrictScalarsArrowAdj φ.hom).homEquiv _ _).symm f))
    (P : SimplicialProjectiveResolution X) (Q : SimplicialProjectiveResolution Y) (j : ℕ) :
    Modules.IsBaseChangeAlong φ.hom (Φ.derivedSemilinearMap φ hφ f P Q j) := by
  have := isIso_homEquiv_symm_derivedBaseChange φ hφ hΦ P j
  have : IsIso (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv _ _).symm
      (Φ.derivedMap φ hφ f P Q j)) := by
    rw [derivedMap, Adjunction.homEquiv_naturality_right_symm]
    infer_instance
  exact Modules.isBaseChangeAlong_of_isIso _ _

end Stacks.SemilinearArrowFunctor
