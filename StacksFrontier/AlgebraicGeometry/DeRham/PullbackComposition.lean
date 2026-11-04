module

public import StacksFrontier.AlgebraicGeometry.DeRham.FormsPushforwardComp
public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.DerivedSectionsPullback
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonAssoc

/-!
# Pullback in de Rham cohomology along a composite of squares

Let

```
X'' --f'--> X' --f--> X
 |p''       |p'       |p
 v          v         v
S'' --g'--> S' --g--> S
```

be two commutative squares of schemes. The pullback maps of Section 0FL6,
`f^* : H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')`, are functorial: the pullback of the outer square is the
pullback of the right square followed by the pullback of the left square. This is what turns a
statement about fibres of `X/S` into one about fibres of `X/Y` for a morphism `X ⟶ Y` over `S`
(as in the proof of [Stacks, Tag 0FUM]).

## Main results

* `AlgebraicGeometry.Scheme.Hom.deRhamCohomologyPullback_comp`: **pullback in de Rham cohomology
  along a composite of squares is the composite of the pullbacks.**
* `AlgebraicGeometry.Scheme.Hom.deRhamDerivedSectionsPullback_comp`: the same on derived global
  sections of the de Rham complexes.
* `AlgebraicGeometry.Scheme.Hom.deRhamAbelianPushforwardMapPlus_comp`: the canonical maps of de
  Rham complexes `Ω^•_{X/S} ⟶ f_*Ω^•_{X'/S'}` of Section 07HX compose.
* `AlgebraicGeometry.Scheme.Hom.derivedSectionsPullback_comp_derivedSectionsPullback`: pullback
  on derived global sections along morphisms of complexes `K ⟶ f_*K'` and `K' ⟶ f'_*K''` composes
  to pullback along `K ⟶ f_*f'_*K'' = (f' ≫ f)_*K''`.
* `Stacks.Cohomology.DerivedPushforwardSections.mapCochainComplexPlusDerivedUnit_comp_compIso_inv`:
  for additive `F`, `G`, `H` with the acyclicity hypotheses of [Stacks, Tag 015M], `H` of the unit
  of `R(G ∘ F)` read through `R(H ∘ G ∘ F) ≅ RH ∘ R(G ∘ F)` is the unit of `RG` read through
  `R(H ∘ G) ≅ RH ∘ RG`, followed by the unit of `RF` read through `R(H ∘ G ∘ F) ≅ R(H ∘ G) ∘ RF`.

## Implementation notes

The derived half is formal: the comparison of [Stacks, Tag 05T2] is associative
(`CategoryTheory.Functor.rightDerivedFunctorPlusComp_assoc_app`) and the derived-functor unit on
bounded-below complexes factors through it
(`CategoryTheory.Functor.mapCochainComplexPlusDerivedUnit_comp`); taking `F = f'_*`, `G = f_*` and
`H = Γ(X, -)` gives the composition law, because `(f' ≫ f)_* = f'_* ⋙ f_*` and
`Γ(X', -) = f_* ⋙ Γ(X, -)` hold definitionally. The underived half is checked degreewise, where
it is `AlgebraicGeometry.Scheme.Hom.deRhamFormsPushforwardHom_comp_apply` on sections.

Several steps compose morphisms whose endpoints are written `(f' ≫ f)_*K` on one side and
`f_*(f'_*K)` on the other (or `((F ⋙ G) ⋙ H)` and `F ⋙ G ⋙ H`); the two agree only by unfolding,
so these steps are made with `Eq.trans`, `whisker_eq` and `eq_whisker`, which are checked at
default transparency, rather than with `rw` or `simp`.

## References

* [Stacks Project, Section 0FL6](https://stacks.math.columbia.edu/tag/0FL6)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Opposite TopologicalSpace
open Stacks.Cohomology.Leray Stacks.Cohomology.LerayLowDegree
open Stacks.Cohomology.DerivedPushforwardSections

universe u

namespace Stacks.Cohomology.DerivedPushforwardSections

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (G : B ⥤ C) (H : C ⥤ D) [F.Additive] [G.Additive] [H.Additive]

/-- The associativity of the comparison of [Stacks, Tag 05T2], read through the isomorphisms
`compIso` of [Stacks, Tag 015M]: `RH` of the comparison `R(G ∘ F) ⟶ RG ∘ RF`, followed by the
inverse of `R(H ∘ G) ≅ RH ∘ RG`, is the inverse of `R(H ∘ G ∘ F) ≅ RH ∘ R(G ∘ F)` followed by
`R(H ∘ G ∘ F) ≅ R(H ∘ G) ∘ RF`. -/
theorem compIso_inv_assoc_app
    (h₁ : ∀ I : A, Injective I → H.rightAcyclic ((F ⋙ G).obj I))
    (h₂ : ∀ I : B, Injective I → H.rightAcyclic (G.obj I))
    (h₃ : ∀ I : A, Injective I → (G ⋙ H).rightAcyclic (F.obj I))
    (K : DerivedCategory.Plus A) :
    H.rightDerivedFunctorPlus.map ((Functor.rightDerivedFunctorPlusComp F G).app K) ≫
        (compIso G H h₂).inv.app (F.rightDerivedFunctorPlus.obj K) =
      (compIso (F ⋙ G) H h₁).inv.app K ≫ (compIso F (G ⋙ H) h₃).hom.app K := by
  rw [← cancel_epi ((compIso (F ⋙ G) H h₁).hom.app K), Iso.hom_inv_id_app_assoc,
    compIso_hom, compIso_hom, reassoc_of% (Functor.rightDerivedFunctorPlusComp_assoc_app F G H K)]
  rw [← compIso_hom G H h₂, Iso.hom_inv_id_app, comp_id]

/-- **The derived-functor unit of a composite, read through the comparisons of
[Stacks, Tag 015M].** `RH` of the unit of `R(G ∘ F)` at a bounded-below complex `M`, followed by
the inverse of `R(H ∘ G ∘ F) ≅ RH ∘ R(G ∘ F)`, is `RH` of the unit of `RG` at `F(M)` followed by
the inverse of `R(H ∘ G) ≅ RH ∘ RG`, then `R(H ∘ G)` of the unit of `RF` at `M` followed by the
inverse of `R(H ∘ G ∘ F) ≅ R(H ∘ G) ∘ RF`. -/
theorem mapCochainComplexPlusDerivedUnit_comp_compIso_inv
    (h₁ : ∀ I : A, Injective I → H.rightAcyclic ((F ⋙ G).obj I))
    (h₂ : ∀ I : B, Injective I → H.rightAcyclic (G.obj I))
    (h₃ : ∀ I : A, Injective I → (G ⋙ H).rightAcyclic (F.obj I))
    (M : CochainComplex.Plus A) :
    H.rightDerivedFunctorPlus.map ((Functor.mapCochainComplexPlusDerivedUnit (F ⋙ G)).app M) ≫
        (compIso (F ⋙ G) H h₁).inv.app (DerivedCategory.Plus.Q.obj M) =
      H.rightDerivedFunctorPlus.map
          ((Functor.mapCochainComplexPlusDerivedUnit G).app (F.mapCochainComplexPlus.obj M)) ≫
        (compIso G H h₂).inv.app (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj M)) ≫
        (G ⋙ H).rightDerivedFunctorPlus.map
          ((Functor.mapCochainComplexPlusDerivedUnit F).app M) ≫
        (compIso F (G ⋙ H) h₃).inv.app (DerivedCategory.Plus.Q.obj M) := by
  have h1 : (compIso (F ⋙ G) H h₁).inv.app (DerivedCategory.Plus.Q.obj M) =
      H.rightDerivedFunctorPlus.map
          ((Functor.rightDerivedFunctorPlusComp F G).app (DerivedCategory.Plus.Q.obj M)) ≫
        (compIso G H h₂).inv.app (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj M)) ≫
        (compIso F (G ⋙ H) h₃).inv.app (DerivedCategory.Plus.Q.obj M) :=
    (Category.comp_id _).symm.trans ((whisker_eq _
      ((compIso F (G ⋙ H) h₃).hom_inv_id_app (DerivedCategory.Plus.Q.obj M))).symm.trans
      ((Category.assoc _ _ _).symm.trans ((eq_whisker
        (compIso_inv_assoc_app F G H h₁ h₂ h₃ (DerivedCategory.Plus.Q.obj M)).symm _).trans
          (Category.assoc _ _ _))))
  have hN := (compIso G H h₂).inv.naturality ((Functor.mapCochainComplexPlusDerivedUnit F).app M)
  dsimp only [Functor.comp_map] at hN
  rw [h1, ← Functor.map_comp_assoc,
    Functor.mapCochainComplexPlusDerivedUnit_comp F G _
      (Functor.rightDerivedFunctorPlusComp_fac F G) M]
  exact (eq_whisker (H.rightDerivedFunctorPlus.map_comp _ _) _).trans
    ((Category.assoc _ _ _).trans (whisker_eq _ ((reassoc_of% hN) _)))

end Stacks.Cohomology.DerivedPushforwardSections

namespace AlgebraicGeometry.Scheme.Hom

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X'' X' X : Scheme.{u}} (f' : X'' ⟶ X') (f : X' ⟶ X)


/-- Derived global sections of the unit of `R(f' ≫ f)_*`, read through the comparison of
[Stacks, Tag 01EZ] for the composite, is the unit of `Rf_*` read through the comparison for `f`
followed by the unit of `Rf'_*` read through the comparison for `f'`. -/
theorem sections_map_derivedUnit_comp_derivedSectionsPushforwardIso_inv
    (M : CochainComplex.Plus (AbelianSheaf X''.toRingedSpace.carrier)) :
    (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        ((Functor.mapCochainComplexPlusDerivedUnit
          (abelianPushforward.{u, u} (f' ≫ f).base)).app M) ≫
        (derivedSectionsPushforwardIso (f' ≫ f)).inv.app (DerivedCategory.Plus.Q.obj M) =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          ((Functor.mapCochainComplexPlusDerivedUnit (abelianPushforward.{u, u} f.base)).app
            ((abelianPushforward.{u, u} f'.base).mapCochainComplexPlus.obj M)) ≫
        (derivedSectionsPushforwardIso f).inv.app
          (DerivedCategory.Plus.Q.obj
            ((abelianPushforward.{u, u} f'.base).mapCochainComplexPlus.obj M)) ≫
        (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          ((Functor.mapCochainComplexPlusDerivedUnit (abelianPushforward.{u, u} f'.base)).app M) ≫
        (derivedSectionsPushforwardIso f').inv.app (DerivedCategory.Plus.Q.obj M) :=
  mapCochainComplexPlusDerivedUnit_comp_compIso_inv (abelianPushforward.{u, u} f'.base)
    (abelianPushforward.{u, u} f.base) (sectionsFunctor X.toRingedSpace.carrier ⊤)
    (rightAcyclic_abelianPushforward_obj (f' ≫ f)) (rightAcyclic_abelianPushforward_obj f)
    (rightAcyclic_abelianPushforward_obj f') M

/-- **Pullback on derived global sections along a composite.** For `φ : K ⟶ f_*K'` on `X` and
`ψ : K' ⟶ f'_*K''` on `X'`, pulling back along `φ` and then along `ψ` is pulling back along the
composite `K ⟶ f_*K' ⟶ f_*f'_*K'' = (f' ≫ f)_*K''`. -/
theorem derivedSectionsPullback_comp_derivedSectionsPullback
    {K : CochainComplex.Plus (AbelianSheaf X.toRingedSpace.carrier)}
    {K' : CochainComplex.Plus (AbelianSheaf X'.toRingedSpace.carrier)}
    {K'' : CochainComplex.Plus (AbelianSheaf X''.toRingedSpace.carrier)}
    (φ : K ⟶ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.obj K')
    (ψ : K' ⟶ (abelianPushforward.{u, u} f'.base).mapCochainComplexPlus.obj K'') :
    derivedSectionsPullback f φ ≫ derivedSectionsPullback f' ψ =
      derivedSectionsPullback (f' ≫ f)
        (φ ≫ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map ψ) := by
  have hu := (Functor.mapCochainComplexPlusDerivedUnit
    (abelianPushforward.{u, u} f.base)).naturality ψ
  have hc := (derivedSectionsPushforwardIso f).inv.naturality (DerivedCategory.Plus.Q.map ψ)
  dsimp only [Functor.comp_map] at hu hc
  have e : (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map
        (φ ≫ (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map ψ)) =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map φ) ≫
        (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map ψ)) := by
    rw [DerivedCategory.Plus.Q.map_comp, Functor.map_comp]
  have key : (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        ((Functor.mapCochainComplexPlusDerivedUnit (abelianPushforward.{u, u} f.base)).app K') ≫
      (derivedSectionsPushforwardIso f).inv.app (DerivedCategory.Plus.Q.obj K') ≫
      (sectionsFunctor X'.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
        (DerivedCategory.Plus.Q.map ψ) =
      (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            ((abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map ψ)) ≫
        (sectionsFunctor X.toRingedSpace.carrier ⊤).rightDerivedFunctorPlus.map
          ((Functor.mapCochainComplexPlusDerivedUnit (abelianPushforward.{u, u} f.base)).app
            ((abelianPushforward.{u, u} f'.base).mapCochainComplexPlus.obj K'')) ≫
        (derivedSectionsPushforwardIso f).inv.app
          (DerivedCategory.Plus.Q.obj
            ((abelianPushforward.{u, u} f'.base).mapCochainComplexPlus.obj K'')) := by
    rw [← hc, ← Functor.map_comp_assoc, ← hu, Functor.map_comp_assoc]
  simp only [derivedSectionsPullback_eq]
  refine Eq.trans ?_ (whisker_eq _
    (sections_map_derivedUnit_comp_derivedSectionsPushforwardIso_inv f' f K'').symm)
  refine Eq.trans ?_ (eq_whisker e _).symm
  simp only [Category.assoc]
  exact whisker_eq _ ((reassoc_of% key) _)

/-- Reassociation used for the degreewise components of extended complexes. -/
private lemma comp_map_inv_comp_map_hom {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {W X : D} {P Q R T : C} (a : W ⟶ X) (b : X ⟶ F.obj P) (i : Q ≅ P) (d : P ⟶ R)
    (j : R ⟶ T) :
    (a ≫ b ≫ F.map i.inv) ≫ F.map (i.hom ≫ d ≫ j) = a ≫ (b ≫ F.map d) ≫ F.map j := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.map_comp_assoc i.inv i.hom, Iso.inv_hom_id, F.map_id, Category.id_comp]

section DeRham

variable {S'' S' S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S') (p'' : X'' ⟶ S'')
  (g : S' ⟶ S) (g' : S'' ⟶ S')

/-- **The canonical maps of de Rham complexes compose**, degreewise: along `X'' ⟶ X' ⟶ X`, the
canonical map `Ω^k_{X/S} ⟶ (f' ≫ f)_*Ω^k_{X''/S''}` of the outer square is the canonical map of
the right square followed by the direct image along `f` of the canonical map of the left one. -/
theorem deRhamAbelianPushforwardMap_comp_f (h : f ≫ p = p' ≫ g) (h' : f' ≫ p' = p'' ≫ g')
    (h'' : (f' ≫ f) ≫ p = p'' ≫ (g' ≫ g)) (k : ℕ) :
    (deRhamAbelianPushforwardMap f p p' g h).f k ≫
        (abelianPushforward.{u, u} f.base).map ((deRhamAbelianPushforwardMap f' p' p'' g' h').f k) =
      (deRhamAbelianPushforwardMap (f' ≫ f) p p'' (g' ≫ g) h'').f k := by
  ext U x
  exact deRhamFormsPushforwardHom_comp_apply f' f p p' p'' g g' h h' h'' k U x

/-- The degree-`k` component of the canonical map of bounded-below de Rham complexes is the
degree-`k` component of the map of complexes, read through the extension isomorphisms. -/
private lemma deRhamAbelianPushforwardMapPlus_hom_f {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (h : f ≫ p = p' ≫ g) (k : ℕ) :
    (deRhamAbelianPushforwardMapPlus f p p' g h).hom.f k =
      (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
        (rfl : ComplexShape.embeddingUpNat.f k = (k : ℤ))).hom ≫
        (deRhamAbelianPushforwardMap f p p' g h).f k ≫
        (abelianPushforward.{u, u} f.base).map
          (HomologicalComplex.extendXIso _ ComplexShape.embeddingUpNat
            (rfl : ComplexShape.embeddingUpNat.f k = (k : ℤ))).inv :=
  HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f
    (abelianPushforward.{u, u} f.base) _ (deRhamAbelianPushforwardMap f p p' g h)
    ComplexShape.embeddingUpNat rfl

/-- **The canonical maps of bounded-below de Rham complexes compose**: along `X'' ⟶ X' ⟶ X`,
the canonical map `Ω^•_{X/S} ⟶ (f' ≫ f)_*Ω^•_{X''/S''}` of the outer square is the canonical
map of the right square followed by the direct image along `f` of the canonical map of the left
one. -/
theorem deRhamAbelianPushforwardMapPlus_comp (h : f ≫ p = p' ≫ g) (h' : f' ≫ p' = p'' ≫ g')
    (h'' : (f' ≫ f) ≫ p = p'' ≫ (g' ≫ g)) :
    deRhamAbelianPushforwardMapPlus f p p' g h ≫
        (abelianPushforward.{u, u} f.base).mapCochainComplexPlus.map
          (deRhamAbelianPushforwardMapPlus f' p' p'' g' h') =
      deRhamAbelianPushforwardMapPlus (f' ≫ f) p p'' (g' ≫ g) h'' := by
  apply ObjectProperty.hom_ext
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  by_cases hi : 0 ≤ i
  · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    refine (congrArg₂ (fun x y => x ≫ (abelianPushforward.{u, u} f.base).map y)
      (deRhamAbelianPushforwardMapPlus_hom_f f p p' g h k)
      (deRhamAbelianPushforwardMapPlus_hom_f f' p' p'' g' h' k)).trans
      (Eq.trans ?_ (deRhamAbelianPushforwardMapPlus_hom_f (f' ≫ f) p p'' (g' ≫ g) h'' k).symm)
    exact (comp_map_inv_comp_map_hom (abelianPushforward.{u, u} f.base) _ _ _ _ _).trans
      (whisker_eq _ (eq_whisker
        (deRhamAbelianPushforwardMap_comp_f f' f p p' p'' g g' h h' h'' k) _))
  · refine (HomologicalComplex.isZero_extend_X _ _ _ (fun j hj => hi ?_)).eq_of_src _ _
    rw [← hj]
    exact Int.natCast_nonneg j

/-- **The pullback maps on derived global sections of the de Rham complex compose**: along
`X'' ⟶ X' ⟶ X` over `S'' ⟶ S' ⟶ S`, the pullback `RΓ(X, Ω^•_{X/S}) ⟶ RΓ(X', Ω^•_{X'/S'})` of
the right square followed by the pullback of the left square is the pullback of the composite
square. -/
theorem deRhamDerivedSectionsPullback_comp (h : f ≫ p = p' ≫ g) (h' : f' ≫ p' = p'' ≫ g')
    (h'' : (f' ≫ f) ≫ p = p'' ≫ (g' ≫ g)) :
    deRhamDerivedSectionsPullback f p p' g h ≫ deRhamDerivedSectionsPullback f' p' p'' g' h' =
      deRhamDerivedSectionsPullback (f' ≫ f) p p'' (g' ≫ g) h'' := by
  rw [deRhamDerivedSectionsPullback_eq, deRhamDerivedSectionsPullback_eq,
    deRhamDerivedSectionsPullback_eq]
  exact (derivedSectionsPullback_comp_derivedSectionsPullback f' f
      (K := SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p)
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p)))
      (K' := SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p')
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p')))
      (K'' := SheafOfModules.deRhamAbelianComplexPlus (deRhamAlgebras p'')
        (SheafOfModules.deRhamDifferential (deRhamAlgebras p'')))
      (deRhamAbelianPushforwardMapPlus f p p' g h)
      (deRhamAbelianPushforwardMapPlus f' p' p'' g' h')).trans
    (congrArg (derivedSectionsPullback (f' ≫ f))
      (deRhamAbelianPushforwardMapPlus_comp f' f p p' p'' g g' h h' h''))

/-- **Pullback in de Rham cohomology is functorial for composites of squares**: along
`X'' ⟶ X' ⟶ X` over `S'' ⟶ S' ⟶ S`, the pullback `H^i_{dR}(X/S) ⟶ H^i_{dR}(X'/S')` of the right
square followed by the pullback `H^i_{dR}(X'/S') ⟶ H^i_{dR}(X''/S'')` of the left square is the
pullback of the composite square. -/
theorem deRhamCohomologyPullback_comp (h : f ≫ p = p' ≫ g) (h' : f' ≫ p' = p'' ≫ g')
    (h'' : (f' ≫ f) ≫ p = p'' ≫ (g' ≫ g)) (i : ℤ) :
    deRhamCohomologyPullback f p p' g h i ≫ deRhamCohomologyPullback f' p' p'' g' h' i =
      deRhamCohomologyPullback (f' ≫ f) p p'' (g' ≫ g) h'' i :=
  ((DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map_comp _ _).symm.trans
    (congrArg (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} i).map
      (deRhamDerivedSectionsPullback_comp f' f p p' p'' g g' h h' h''))

end DeRham

end AlgebraicGeometry.Scheme.Hom

end
