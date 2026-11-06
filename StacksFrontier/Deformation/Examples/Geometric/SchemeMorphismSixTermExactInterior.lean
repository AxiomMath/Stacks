module

public import StacksFrontier.Deformation.Applications.InfinitesimalAutomorphismTransfer
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismFiberAutPair
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismSixTermInteriorSourceCross
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismsRimSchlessingerUnconditional
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismEndpointsSupplied

/-!
# The interior of the sequence of Stacks 0E3V at the canonical data

For a morphism `f : X → Y` of schemes over `k` there is a six-term exact sequence

```
0 → Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X)
  → T Def_{X → Y} → T(Def_X × Def_Y) → Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)
```

whose arrows are read at the trivial deformation `f' : X' → Y'` of `f` over `k[ε]`. The `Inf`
terms are tangent spaces of automorphism functors, defined relative to a choice of pushforwards of
the base point. This file fixes that choice for `Def_{X → Y}`, takes for `Def_X` and `Def_Y` its
images under the two forgetful functors, and proves exactness at the second, third and fourth
spots at the resulting data, which depends only on `f`.

## Main definitions

* `Deformation.ChosenPushforwardsAt.ofComp`: the pushforwards of `Φ(x₀)` obtained by applying a
  functor `Φ` to chosen pushforwards of `x₀`.
* `Deformation.Examples.schemeMorphismTrivialObject`: the base point `(k, X → Y)` of
  `Def_{X → Y}`.
* `Deformation.Examples.schemeMorphismTrivialPushforwards`: the fixed choice of pushforwards of
  that base point, and `Deformation.Examples.schemeMorphismSourcePushforwards`,
  `Deformation.Examples.schemeMorphismTargetPushforwards`: its source and target endpoints, the
  fixed choices for `Def_X` and `Def_Y`.
* `Deformation.Examples.schemeMorphismTrivialLift`: the trivial lift `f' = f × id : X' → Y'`.

## Main results

* `Deformation.Examples.liftClass_schemeMorphismTrivialLift`: the trivial lift has class zero.
* `Deformation.Examples.exists_schemeMorphismInfinitesimalPair'_eq_iff`: the image of the canonical
  arrow `Inf(Def_{X → Y}) → Inf(Def_X × Def_Y)` is the set of pairs compatible with `f'`.
* `Deformation.Examples.exact_schemeMorphismInfinitesimalPair'_conjDerivationCross`: exactness at
  the second spot.
* `Deformation.Examples.exact_schemeMorphismSixTerm_thirdFourthSpot_canonical`: exactness at the
  third and fourth spots.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 06JT](https://stacks.math.columbia.edu/tag/06JT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation

section Transport

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (Φ : F ⥤ G) {x₀ : F}
  (P : ChosenPushforwardsAt (Φ ⋙ q) x₀) (Q : ChosenPushforwardsAt q (Φ.obj x₀))

/-- The induced map on infinitesimal automorphisms, transported to another coordinate object:
the transport of the image is the conjugate, by the comparison of pushforwards, of the image of the
transport. -/
public theorem transportAut_inducedInfinitesimalFun (hq : IsCofiberedInGroupoids q)
    {V : Under ((Φ ⋙ q).obj x₀)} (ι : dualNumbersUnder (p := Φ ⋙ q) (x := x₀) ⟶ V)
    (a : localizedAutomorphismFunctorTangent P) :
    (Q.transportAut ι (localizedTangentEquivKernel Q (inducedInfinitesimalFun Φ P Q hq
        a)).1).asIso.hom.val =
      comparisonPushforward Φ P Q V ≫
        Φ.map (P.transportAut ι (localizedTangentEquivKernel P a).1).asIso.hom.val ≫
          comparisonPushforwardInv Φ P Q hq V := by
  have h : (localizedTangentEquivKernel Q (inducedInfinitesimalFun Φ P Q hq a)).1 =
      inducedAutomorphismHom Φ P Q hq _ (localizedTangentEquivKernel P a).1 :=
    congrArg Subtype.val (localizedTangentEquivKernel_inducedInfinitesimalFun Φ P Q hq a)
  rw [h, ← inducedAutomorphismHom_transportAut, inducedAutomorphismHom_hom_val]

end Transport

section OfComp

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {C : Type u₃} [Category.{v₃} C] {q : G ⥤ C} (Φ : F ⥤ G) {x₀ : F}

/-- The chosen pushforwards of `Φ(x₀)` obtained by applying `Φ` to chosen pushforwards of `x₀`. -/
@[implicit_reducible]
public def ChosenPushforwardsAt.ofComp (hq : IsCofiberedInGroupoids q)
    (P : ChosenPushforwardsAt (Φ ⋙ q) x₀) : ChosenPushforwardsAt q (Φ.obj x₀) :=
  ChosenPushforwardsAt.ofCofiberedInGroupoids hq (fun U => ⟨Φ.obj (P.obj U).1, (P.obj U).2⟩)
    (fun U => Φ.map (P.inclusion U)) (fun U => isHomLift_map_inclusion Φ P U)

variable (hq : IsCofiberedInGroupoids q) (P : ChosenPushforwardsAt (Φ ⋙ q) x₀)

/-- For the pushforwards obtained by applying `Φ`, the canonical arrows are the images of the
canonical arrows. -/
public theorem ChosenPushforwardsAt.ofComp_map {U V : Under ((Φ ⋙ q).obj x₀)} (g : U ⟶ V) :
    (P.ofComp Φ hq).map g = Φ.map (P.map g) := by
  let := (P.ofComp Φ hq).inclusion_cocartesian U
  let : q.IsHomLift g.right (Φ.map (P.map g)) := isHomLift_map_of_comp Φ g.right (P.map g)
    (P.map_isHomLift g)
  refine Functor.IsStronglyCocartesian.ext q U.hom ((P.ofComp Φ hq).inclusion U) g.right ?_
  rw [ChosenPushforwardsAt.inclusion_map]
  show Φ.map (P.inclusion V) = Φ.map (P.inclusion U) ≫ Φ.map (P.map g)
  rw [← Φ.map_comp, P.inclusion_map]

/-- For the pushforwards obtained by applying `Φ`, the comparison of pushforwards is the
identity. -/
@[simp]
public theorem comparisonPushforward_ofComp (U : Under ((Φ ⋙ q).obj x₀)) :
    comparisonPushforward Φ P (P.ofComp Φ hq) U = 𝟙 _ := by
  let := (P.ofComp Φ hq).inclusion_cocartesian U
  let : q.IsHomLift (𝟙 U.right) (𝟙 ((P.ofComp Φ hq).obj U).1) :=
    IsHomLift.id ((P.ofComp Φ hq).obj U).2
  refine Functor.IsStronglyCocartesian.ext q U.hom ((P.ofComp Φ hq).inclusion U) (𝟙 U.right) ?_
  rw [inclusion_comp_comparisonPushforward, Category.comp_id]
  rfl

/-- For the pushforwards obtained by applying `Φ`, the inverse comparison is the identity. -/
@[simp]
public theorem comparisonPushforwardInv_ofComp (U : Under ((Φ ⋙ q).obj x₀)) :
    comparisonPushforwardInv Φ P (P.ofComp Φ hq) hq U = 𝟙 _ := by
  have h := comparisonPushforward_comp_inv Φ P (P.ofComp Φ hq) hq U
  rwa [comparisonPushforward_ofComp, Category.id_comp] at h

end OfComp

section OfCompTransport

universe u v w u₁ v₁ u₂ v₂

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {G : Type u₂} [Category.{v₂} G]
  {q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (Φ : F ⥤ G) {x₀ : F}
  (hq : IsCofiberedInGroupoids q) (P : ChosenPushforwardsAt (Φ ⋙ q) x₀)

/-- For the pushforwards obtained by applying `Φ`, the transport of the image of an infinitesimal
automorphism is the image of its transport. -/
public theorem transportAut_ofComp_inducedInfinitesimalFun {V : Under ((Φ ⋙ q).obj x₀)}
    (ι : dualNumbersUnder (p := Φ ⋙ q) (x := x₀) ⟶ V)
    (a : localizedAutomorphismFunctorTangent P) :
    ((P.ofComp Φ hq).transportAut ι (localizedTangentEquivKernel (P.ofComp Φ hq)
        (inducedInfinitesimalFun Φ P (P.ofComp Φ hq) hq a)).1).asIso.hom.val =
      Φ.map (P.transportAut ι (localizedTangentEquivKernel P a).1).asIso.hom.val := by
  rw [transportAut_inducedInfinitesimalFun, comparisonPushforward_ofComp,
    comparisonPushforwardInv_ofComp, Category.id_comp, Category.comp_id]

end OfCompTransport

section FiberCongr

universe u₁ v₁ u₂ v₂

/-- Re-indexing the fibre containing an object along an equality of base objects does not change
its automorphism group. -/
public def fiberAutCongr {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒮 : Type u₂} [Category.{v₂} 𝒮]
    {p : 𝒳 ⥤ 𝒮}
    (a : 𝒳) {S S' : 𝒮} (h : p.obj a = S) (h' : p.obj a = S') :
    @Aut (p.Fiber S) _ ⟨a, h⟩ ≃ @Aut (p.Fiber S') _ ⟨a, h'⟩ := by
  subst h h'
  exact Equiv.refl _

/-- The re-indexing `fiberAutCongr` does not change the underlying morphism. -/
@[simp]
public theorem fiberAutCongr_hom_val {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒮 : Type u₂}
    [Category.{v₂} 𝒮] {p : 𝒳 ⥤ 𝒮} (a : 𝒳) {S S' : 𝒮} (h : p.obj a = S) (h' : p.obj a = S')
    (g : @Aut (p.Fiber S) _ ⟨a, h⟩) :
    (fiberAutCongr a h h' g).asIso.hom.val = g.asIso.hom.val := by
  subst h h'
  rfl

end FiberCongr

namespace Examples

universe u

attribute [local instance] deformationSpecialMap_isClosedImmersion
  residueSpecMap_isClosedImmersion

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (pX : X ⟶ baseSpec (residueFieldBase Λ k)) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))
  (hf : f ≫ pY = pX)

/-- The trivial deformation of `f` over the residue field: the base point `x₀ = (k, X → Y)` of
`Def_{X → Y}`. -/
def schemeMorphismTrivialObject : schemeMorphismDeformationCategory f pX pY hf :=
  Over.mk (𝟙 _)

/-- The chosen pushforwards of the base point of `Def_{X ⟶ Y}`, fixed once and for all. -/
def schemeMorphismTrivialPushforwards :
    ChosenPushforwardsAt (schemeMorphismDeformationCategoryProjection f pX pY hf)
      (schemeMorphismTrivialObject f pX pY hf) :=
  chosenPushforwardsAt (schemeMorphismDeformationCategoryProjection_cofiberedInGroupoids f pX pY hf)
    _

/-- The chosen pushforwards of the base point of `Def_X`: the source endpoints of the chosen
pushforwards of the base point of `Def_{X ⟶ Y}`. -/
def schemeMorphismSourcePushforwards :
    ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      ((schemeMorphismSourceForgetful f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf)) :=
  ChosenPushforwardsAt.ofComp (schemeMorphismSourceForgetful f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
    (schemeMorphismTrivialPushforwards f pX pY hf)

/-- The chosen pushforwards of the base point of `Def_Y`: the target endpoints of the chosen
pushforwards of the base point of `Def_{X ⟶ Y}`. -/
def schemeMorphismTargetPushforwards :
    ChosenPushforwardsAt (schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      ((schemeMorphismTargetForgetful f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf)) :=
  ChosenPushforwardsAt.ofComp (schemeMorphismTargetForgetful f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
    (schemeMorphismTrivialPushforwards f pX pY hf)

/-- The trivial first-order deformation of `f` over the re-based dual numbers. -/
abbrev schemeMorphismTrivialFirstOrder : schemeMorphismDeformationCategory f pX pY hf :=
  ((schemeMorphismTrivialPushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
    ((schemeMorphismDeformationCategoryProjection f pX pY hf).obj
      (schemeMorphismTrivialObject f pX pY hf)) (FGModuleCat.of k (ULift.{u} k)))).1

/-- The arrow of a deformation of `f` is a lift of `f` to its two endpoint deformations. -/
def schemeMorphismEndpointsLift (m : schemeMorphismDeformationCategory f pX pY hf)
    (h : ((schemeMorphismTargetForgetful f pX pY hf).obj m).base =
      ((schemeMorphismSourceForgetful f pX pY hf).obj m).base) :
    globalLiftsOverBase f ((schemeMorphismSourceForgetful f pX pY hf).obj m)
      ((schemeMorphismTargetForgetful f pX pY hf).obj m) (eqToHom h) :=
  ⟨m.left.morphism, by
    have key : ∀ e : m.left.base ⟶ m.left.base, e = 𝟙 _ →
        m.left.morphism ≫ m.left.targetToBase = m.left.sourceToBase ≫ baseSpecMap e := by
      rintro e rfl
      rw [baseSpecMap_id, Category.comp_id]
      exact m.left.over_base
    exact key (eqToHom h) (eqToHom_refl m.left.base h),
   m.hom.source_pullback.w.symm⟩

/-- The underlying morphism of `schemeMorphismEndpointsLift` is the arrow of the deformation. -/
@[simp]
theorem schemeMorphismEndpointsLift_val (m : schemeMorphismDeformationCategory f pX pY hf)
    (h : ((schemeMorphismTargetForgetful f pX pY hf).obj m).base =
      ((schemeMorphismSourceForgetful f pX pY hf).obj m).base) :
    (schemeMorphismEndpointsLift f pX pY hf m h).1 = m.left.morphism := rfl

/-- The trivial lift `f' = f × id : X' → Y'`: the arrow of the trivial first-order deformation of
`f`, read as a lift of `f` to the trivial first-order deformations of its two endpoints. -/
def schemeMorphismTrivialLift :
    globalLiftsOverBase f (firstOrderPushforwardCross (schemeMorphismSourcePushforwards f pX pY hf))
      (firstOrderPushforwardCross (schemeMorphismTargetPushforwards f pX pY hf))
      (eqToHom ((firstOrderPushforwardCross_base _).trans
        (firstOrderPushforwardCross_base _).symm)) :=
  schemeMorphismEndpointsLift f pX pY hf (schemeMorphismTrivialFirstOrder f pX pY hf) _

/-- The class of the trivial deformation of a scheme over the re-based dual numbers vanishes. -/
theorem tangentClassAt_firstOrderPushforwardCross_eq_zero {Z : Over (Spec (CommRingCat.of k))}
    (hZ : IsDeformationCategory.{u, u, u}
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z))
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) Z}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z) x₀) :
    tangentClassAt.{u, u, u} (BasedCategory.ofFunctor
        (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z)) hZ
        (FGModuleCat.of k (ULift.{u} k))
        ⟨firstOrderPushforwardCross P, firstOrderPushforwardCross_base P⟩ = 0 :=
  tangentClassAt_pushforward_eq_zero.{u, u, u} (BasedCategory.ofFunctor
    (schemeDeformationCategoryProjection (Λ := Λ) (k := k) Z)) hZ x₀ P
    (FGModuleCat.of k (ULift.{u} k))

/-- The lift given by the arrow of the trivial deformation of `f` over `k[N]` has class zero. -/
private theorem liftClass_schemeMorphismEndpointsLift_trivial
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) (N : FGModuleCat.{u} k)
    (m : schemeMorphismDeformationCategory f pX pY hf)
    (hm : m = ((schemeMorphismTrivialPushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
      ((schemeMorphismDeformationCategoryProjection f pX pY hf).obj
        (schemeMorphismTrivialObject f pX pY hf)) N)).1)
    (h : ((schemeMorphismTargetForgetful f pX pY hf).obj m).base =
      ((schemeMorphismSourceForgetful f pX pY hf).obj m).base)
    (hQ : ((schemeMorphismTargetForgetful f pX pY hf).obj m).base =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N) :
    liftClass f pX pY hf hM N hQ (schemeMorphismEndpointsLift f pX pY hf m h) = 0 := by
  subst hm
  refine ((tangentClassAt_eq_iff.{u, u, u} _ hM _ _ _).mpr ?_).trans
    (tangentClassAt_pushforward_eq_zero.{u, u, u} (BasedCategory.ofFunctor
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) hM
      (schemeMorphismTrivialObject f pX pY hf) (schemeMorphismTrivialPushforwards f pX pY hf) N)
  refine isIsomorphic_liftDeformationFiberObject_of_familyHom f pX pY hf hM _ _ _
    ((schemeMorphismTrivialPushforwards f pX pY hf).obj _).2 (𝟙 _) (𝟙 _) (𝟙 _)
    (IsPullback.id_vert _) ?_ (Category.comp_id _) (Category.comp_id _) ?_
  · have key : ∀ {A : ArtinianLocalAlgCat.{u, u, u} Λ k} {S : Scheme.{u}} (t : S ⟶ baseSpec A),
        IsPullback (𝟙 S) t t (baseSpecMap (𝟙 A)) := fun t => by
      rw [baseSpecMap_id]
      exact IsPullback.id_horiz t
    exact key _
  · simp only [eqToHom_trans, Category.id_comp]
    exact (eqToHom_refl _ _).symm

/-- The trivial lift has class zero in `T Def_{X ⟶ Y}`. -/
theorem liftClass_schemeMorphismTrivialLift
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) :
    liftClass f pX pY hf hM (FGModuleCat.of k (ULift.{u} k)) (firstOrderPushforwardCross_base _)
      (schemeMorphismTrivialLift f pX pY hf) = 0 :=
  liftClass_schemeMorphismEndpointsLift_trivial f pX pY hf hM _ _ rfl _ _

/-- The comparison of the dual numbers under the base of the trivial deformation of `f` with the
re-based dual numbers. -/
abbrev schemeMorphismDualCrossIso :=
  squareZeroCrossUnderIso.{u, u, u}
    ((schemeMorphismDeformationCategoryProjection f pX pY hf).obj
      (schemeMorphismTrivialObject f pX pY hf)) (FGModuleCat.of k (ULift.{u} k))

/-- An infinitesimal automorphism of the trivial deformation of `f`, transported to the re-based
dual numbers. -/
abbrev schemeMorphismInfinitesimalAutCross
    (x : localizedAutomorphismFunctorTangent (schemeMorphismTrivialPushforwards f pX pY hf)) :
    Aut ((schemeMorphismTrivialPushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
      ((schemeMorphismDeformationCategoryProjection f pX pY hf).obj
        (schemeMorphismTrivialObject f pX pY hf)) (FGModuleCat.of k (ULift.{u} k)))) :=
  (schemeMorphismTrivialPushforwards f pX pY hf).transportAut
    (schemeMorphismDualCrossIso f pX pY hf).hom
    (localizedTangentEquivKernel (schemeMorphismTrivialPushforwards f pX pY hf) x).1

/-- The source component of the arrow `a`, as a self-map of the trivial first-order deformation
of `X`, is the source component of the infinitesimal automorphism of the trivial deformation of
`f`. -/
theorem localizedTangentEquivSelfMapsCross_infinitesimalPair_fst
    (x : localizedAutomorphismFunctorTangent (schemeMorphismTrivialPushforwards f pX pY hf)) :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    (localizedTangentEquivSelfMapsCross
        (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
        pX))
        (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismInfinitesimalPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
        (schemeMorphismTrivialPushforwards f pX pY hf) (schemeMorphismSourcePushforwards f pX pY hf)
        (schemeMorphismTargetPushforwards f pX pY hf) x).1).1 =
      (schemeMorphismInfinitesimalAutCross f pX pY hf x).asIso.hom.val.left.source :=
  congrArg SchemeDeformationCategory.Hom.map
    (transportAut_ofComp_inducedInfinitesimalFun
      (q := schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX))
      (schemeMorphismSourceForgetful f pX pY hf)
      (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
      (schemeMorphismTrivialPushforwards f pX pY hf) (schemeMorphismDualCrossIso f pX pY hf).hom x)

/-- The target component of the arrow `a`, as a self-map of the trivial first-order deformation
of `Y`. -/
theorem localizedTangentEquivSelfMapsCross_infinitesimalPair_snd
    (x : localizedAutomorphismFunctorTangent (schemeMorphismTrivialPushforwards f pX pY hf)) :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    (localizedTangentEquivSelfMapsCross
        (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
        pY))
        (schemeMorphismTargetPushforwards f pX pY hf) (schemeMorphismInfinitesimalPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
        (schemeMorphismTrivialPushforwards f pX pY hf) (schemeMorphismSourcePushforwards f pX pY hf)
        (schemeMorphismTargetPushforwards f pX pY hf) x).2).1 =
      (schemeMorphismInfinitesimalAutCross f pX pY hf x).asIso.hom.val.left.target :=
  congrArg SchemeDeformationCategory.Hom.map
    (transportAut_ofComp_inducedInfinitesimalFun
      (q := schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY))
      (schemeMorphismTargetForgetful f pX pY hf)
      (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
      (schemeMorphismTrivialPushforwards f pX pY hf) (schemeMorphismDualCrossIso f pX pY hf).hom x)

/-- The image of the arrow `a = schemeMorphismInfinitesimalPair'` from `Inf(Def_{X → Y})` to
`Inf(Def_X × Def_Y)`, at the canonical data: a pair of infinitesimal automorphisms of the trivial
first-order deformations of `X` and `Y`, read as a pair of self-maps `(α, β)` of the trivial
first-order deformations over the re-based dual numbers, is in the image of `a` exactly when it is
compatible with the trivial lift `f'`, that is `f' ∘ α = β ∘ f'`. -/
theorem exists_schemeMorphismInfinitesimalPair'_eq_iff
    (t : localizedAutomorphismFunctorTangent (schemeMorphismSourcePushforwards f pX pY hf) ×
        localizedAutomorphismFunctorTangent (schemeMorphismTargetPushforwards f pX pY hf)) :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    (∃ x, schemeMorphismInfinitesimalPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
        (schemeMorphismTrivialPushforwards f pX pY hf) (schemeMorphismSourcePushforwards f pX pY hf)
        (schemeMorphismTargetPushforwards f pX pY hf) x = t) ↔
      (schemeMorphismTrivialLift f pX pY hf).1 ≫ (localizedTangentEquivSelfMapsCross
          (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
          pY)) (schemeMorphismTargetPushforwards f pX pY hf) t.2).1 =
        (localizedTangentEquivSelfMapsCross
            (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
            pX)) (schemeMorphismSourcePushforwards f pX pY hf) t.1).1 ≫
                (schemeMorphismTrivialLift f pX pY hf).1 := by
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
  constructor
  · rintro ⟨x, rfl⟩
    rw [localizedTangentEquivSelfMapsCross_infinitesimalPair_fst,
      localizedTangentEquivSelfMapsCross_infinitesimalPair_snd]
    exact (schemeMorphismInfinitesimalAutCross f pX pY hf x).asIso.hom.val.left.source_pullback.w
  · intro hcomm
    set α := localizedTangentEquivSelfMapsCross
        (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
        pX)) (schemeMorphismSourcePushforwards f pX pY hf) t.1 with hα
    set β := localizedTangentEquivSelfMapsCross
        (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
        pY)) (schemeMorphismTargetPushforwards f pX pY hf) t.2 with hβ
    let N := schemeMorphismTrivialFirstOrder f pX pY hf
    let E := morphismFiberAutEquivSelfMapPairs f pX pY hf N
    let pr : { p : (N.left.source ⟶ N.left.source) × (N.left.target ⟶ N.left.target) //
        IsIso p.1 ∧ IsIso p.2 ∧ p.2 ≫ N.left.targetToBase = N.left.targetToBase ∧
          N.hom.source ≫ p.1 = N.hom.source ∧ N.hom.target ≫ p.2 = N.hom.target ∧
          N.left.morphism ≫ p.2 = p.1 ≫ N.left.morphism } :=
      ⟨(α.1, β.1), α.2.2.2, β.2.2.2, β.2.1, α.2.2.1, β.2.2.1, hcomm⟩
    let y : Aut ((schemeMorphismTrivialPushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
        ((schemeMorphismDeformationCategoryProjection f pX pY hf).obj
          (schemeMorphismTrivialObject f pX pY hf)) (FGModuleCat.of k (ULift.{u} k)))) :=
      fiberAutCongr N rfl ((schemeMorphismTrivialPushforwards f pX pY hf).obj _).2 (E.symm pr)
    have hy : y.asIso.hom.val.left.source = α.1 ∧ y.asIso.hom.val.left.target = β.1 := by
      have h := congrArg Subtype.val (E.apply_symm_apply pr)
      rw [morphismFiberAutEquivSelfMapPairs_apply] at h
      have hv : y.asIso.hom.val = (E.symm pr).asIso.hom.val := fiberAutCongr_hom_val _ _ _ _
      exact ⟨(congrArg (fun g => g.left.source) hv).trans (congrArg Prod.fst h),
        (congrArg (fun g => g.left.target) hv).trans (congrArg Prod.snd h)⟩
    have hmem : (schemeMorphismTrivialPushforwards f pX pY hf).transportAut
        (schemeMorphismDualCrossIso f pX pY hf).inv y ∈
          MonoidHom.ker ((schemeMorphismTrivialPushforwards f pX pY hf).transportAutHom
            (tangentReduction (p := schemeMorphismDeformationCategoryProjection f pX pY hf)
              (x := schemeMorphismTrivialObject f pX pY hf))) := by
      rw [ker_transportAutHom_eq_top_of_isThin
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
            hf).predeformation.cofibered
        _ (isThin_specialFiber
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY
              hf).predeformation)]
      exact Subgroup.mem_top _
    let x := (localizedTangentEquivKernel (schemeMorphismTrivialPushforwards f pX pY hf)).symm
      ⟨_, hmem⟩
    have hx : schemeMorphismInfinitesimalAutCross f pX pY hf x = y := by
      show (schemeMorphismTrivialPushforwards f pX pY hf).transportAut _
        (localizedTangentEquivKernel _ ((localizedTangentEquivKernel _).symm ⟨_, hmem⟩)).1 = y
      rw [Equiv.apply_symm_apply]
      exact ChosenPushforwardsAt.transportAut_hom_transportAut_inv _ _ y
    refine ⟨x, Prod.ext ?_ ?_⟩
    · refine (localizedTangentEquivSelfMapsCross
        (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
        pX)) (schemeMorphismSourcePushforwards f pX pY hf)).injective (Subtype.ext ?_)
      rw [localizedTangentEquivSelfMapsCross_infinitesimalPair_fst, hx]
      exact hy.1
    · refine (localizedTangentEquivSelfMapsCross
        (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
        pY)) (schemeMorphismTargetPushforwards f pX pY hf)).injective (Subtype.ext ?_)
      rw [localizedTangentEquivSelfMapsCross_infinitesimalPair_snd, hx]
      exact hy.2

/-- Exactness of `Inf(Def_{X → Y}) → Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X)` at the canonical
data: the image of the arrow `a = schemeMorphismInfinitesimalPair'` is the kernel of the arrow `b`
sending a pair of infinitesimal automorphisms of the endpoints to the unique derivation carrying
the trivial lift where the pair carries it. -/
theorem exact_schemeMorphismInfinitesimalPair'_conjDerivationCross :
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
    letI := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    letI := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
      (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
    Function.Exact (schemeMorphismInfinitesimalPair' f pX pY hf
        (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
        (schemeMorphismTrivialPushforwards f pX pY hf) (schemeMorphismSourcePushforwards f pX pY hf)
        (schemeMorphismTargetPushforwards f pX pY hf))
      (globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf
          (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
          pX)) (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k)
              (Over.mk pY)) (schemeMorphismSourcePushforwards f pX pY hf)
              (schemeMorphismTargetPushforwards f pX pY hf)
        (firstOrderPushforwardCrossConormalIsoUnit (schemeMorphismSourcePushforwards f pX pY
            hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
                (schemeMorphismSourcePushforwards f pX pY hf))
                (schemeMorphismTrivialLift f pX pY hf)) := by
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismTrivialPushforwards f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismTrivialPushforwards f pX pY hf)
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismSourcePushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismSourcePushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX)).satisfiesRS
  let := naturalLocalizedTangentAddCommGroup (schemeMorphismTargetPushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
  let := naturalLocalizedTangentModule (schemeMorphismTargetPushforwards f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY)).satisfiesRS
  refine exact_fst_of_simplyTransitive
    (globalLiftsOverBaseDerivationVAdd f pX pY hf (firstOrderPushforwardCrossConormalIsoUnit
        (schemeMorphismSourcePushforwards f pX pY
        hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
            (schemeMorphismSourcePushforwards f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf))
    (fun t => globalLiftsOverBaseAutPairConj f pX pY
      (localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross pX pY
          (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
          pX)) (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k)
              (Over.mk pY)) (schemeMorphismSourcePushforwards f pX pY hf)
              (schemeMorphismTargetPushforwards f pX pY hf) _ t))
    (schemeMorphismTrivialLift f pX pY hf)
    (globalLiftsOverBaseDerivationVAdd_zero f pX pY hf (firstOrderPushforwardCrossConormalIsoUnit
        (schemeMorphismSourcePushforwards f pX pY
        hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
            (schemeMorphismSourcePushforwards f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf))
    (existsUnique_globalLiftsOverBaseDerivationVAdd f pX pY hf
        (firstOrderPushforwardCrossConormalIsoUnit (schemeMorphismSourcePushforwards f pX pY
        hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
            (schemeMorphismSourcePushforwards f pX pY hf))
            (schemeMorphismTrivialLift f pX pY hf)) _ _
    (fun t => globalLiftsOverBaseDerivationVAdd_conjDerivation f pX pY hf
        (firstOrderPushforwardCrossConormalIsoUnit (schemeMorphismSourcePushforwards f pX pY
        hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
            (schemeMorphismSourcePushforwards f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf) _)
    (fun t => ?_)
  rw [globalLiftsOverBaseAutPairConj_eq_iff,
    localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross_fst_val,
    localizedTangentPairEquivGlobalLiftsOverBaseAutPairCross_snd_val]
  exact exists_schemeMorphismInfinitesimalPair'_eq_iff f pX pY hf t

/-- Exactness of `Inf(Def_X × Def_Y) → Der_k(𝒪_Y, f_*𝒪_X) → T Def_{X → Y} → T(Def_X × Def_Y)`
at its two interior terms, at the canonical data. -/
theorem exact_schemeMorphismSixTerm_thirdFourthSpot_canonical :
    Function.Exact
        (globalLiftsOverBaseConjDerivationLocalizedTangentCross f pX pY hf
            (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk
            pX)) (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k)
                (Over.mk pY)) (schemeMorphismSourcePushforwards f pX pY hf)
                (schemeMorphismTargetPushforwards f pX pY hf)
          (firstOrderPushforwardCrossConormalIsoUnit (schemeMorphismSourcePushforwards f pX pY
              hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
                  (schemeMorphismSourcePushforwards f pX pY hf))
                  (schemeMorphismTrivialLift f pX pY hf))
        (schemeMorphismDerivationTangentMap f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
          (FGModuleCat.of k (ULift.{u} k)) (firstOrderPushforwardCross_base
              (schemeMorphismTargetPushforwards f pX pY hf))
          (globalLiftsOverBaseDerivationVAdd f pX pY hf (firstOrderPushforwardCrossConormalIsoUnit
              (schemeMorphismSourcePushforwards f pX pY
              hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
                  (schemeMorphismSourcePushforwards f pX pY hf))
                  (schemeMorphismTrivialLift f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf)) ∧
      Function.Exact
        (schemeMorphismDerivationTangentMap f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
          (FGModuleCat.of k (ULift.{u} k)) (firstOrderPushforwardCross_base
              (schemeMorphismTargetPushforwards f pX pY hf))
          (globalLiftsOverBaseDerivationVAdd f pX pY hf (firstOrderPushforwardCrossConormalIsoUnit
              (schemeMorphismSourcePushforwards f pX pY
              hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
                  (schemeMorphismSourcePushforwards f pX pY hf))
                  (schemeMorphismTrivialLift f pX pY hf)) (schemeMorphismTrivialLift f pX pY hf))
        (schemeMorphismTangentPair' f pX pY hf
          (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
          (FGModuleCat.of k (ULift.{u} k))) :=
  exact_schemeMorphismSixTerm_thirdFourthSpot_localizedTangent f pX pY hf
      (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk pX))
      (schemeDeformationCategoryProjection_isPredeformationCategory (Λ := Λ) (k := k) (Over.mk pY))
      (schemeMorphismSourcePushforwards f pX pY hf) (schemeMorphismTargetPushforwards f pX pY hf)
    (firstOrderPushforwardCrossConormalIsoUnit (schemeMorphismSourcePushforwards f pX pY
        hf)) (firstOrderPushforwardCross_maximalIdeal_pow_two
            (schemeMorphismSourcePushforwards f pX pY hf))
            (isDeformationCategory_schemeMorphismDeformationCategoryProjection f pX pY hf)
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pX))
    (isDeformationCategory_schemeDeformationCategoryProjection (Over.mk pY))
    (tangentClassAt_firstOrderPushforwardCross_eq_zero _ (schemeMorphismSourcePushforwards f pX pY
        hf))
    (tangentClassAt_firstOrderPushforwardCross_eq_zero _ (schemeMorphismTargetPushforwards f pX pY
        hf)) (schemeMorphismTrivialLift f pX pY hf)
    (liftClass_schemeMorphismTrivialLift f pX pY hf _)

/-! ### The trivial deformations at an arbitrary coordinate module -/

section CoordinateModule

variable (N : FGModuleCat.{u} k)

/-- The maximal ideal of the square-zero extension `k[N]` has square zero. -/
theorem maximalIdeal_squareZeroExtensionArtinian_pow_two :
    IsLocalRing.maximalIdeal ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N : Type u) ^ 2
      = ⊥ := by
  let : Module kᵐᵒᵖ N :=
    Module.compHom N {
      toFun := MulOpposite.unop
      map_one' := rfl
      map_mul' := by simp [mul_comm]
      map_zero' := rfl
      map_add' := by intros; rfl }
  let : IsCentralScalar k N := ⟨fun _ _ => rfl⟩
  let r : ((squareZeroExtensionArtinian.{u, u, u} Λ k).obj N : Type u) →+* k :=
    (TrivSqZeroExt.fstHom k k N).toRingHom
  rw [← IsLocalRing.ker_eq_maximalIdeal r fun a ↦ ⟨TrivSqZeroExt.inl a, rfl⟩]
  exact TrivSqZeroExt.kerIdeal_sq k N

/-- The trivial deformation of `X` over the re-based square-zero extension `k[N]`. -/
abbrev schemeMorphismSourceTrivialAt : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pX) :=
  ((schemeMorphismSourcePushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
    ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pX)).obj
      ((schemeMorphismSourceForgetful f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf)))
    N)).1

/-- The trivial deformation of `Y` over the re-based square-zero extension `k[N]`. -/
abbrev schemeMorphismTargetTrivialAt : SchemeDeformationCategory (Λ := Λ) (k := k) (Over.mk pY) :=
  ((schemeMorphismTargetPushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
    ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) (Over.mk pY)).obj
      ((schemeMorphismTargetForgetful f pX pY hf).obj (schemeMorphismTrivialObject f pX pY hf)))
    N)).1

/-- The trivial deformation of `X` over `k[N]` lies over `k[N]`. -/
theorem schemeMorphismSourceTrivialAt_base :
    (schemeMorphismSourceTrivialAt f pX pY hf N).base =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N :=
  ((schemeMorphismSourcePushforwards f pX pY hf).obj _).2

/-- The trivial deformation of `Y` over `k[N]` lies over `k[N]`. -/
theorem schemeMorphismTargetTrivialAt_base :
    (schemeMorphismTargetTrivialAt f pX pY hf N).base =
      (squareZeroExtensionArtinian.{u, u, u} Λ k).obj N :=
  ((schemeMorphismTargetPushforwards f pX pY hf).obj _).2

/-- The trivial deformation of `f` over the re-based square-zero extension `k[N]`. -/
abbrev schemeMorphismTrivialFirstOrderAt : schemeMorphismDeformationCategory f pX pY hf :=
  ((schemeMorphismTrivialPushforwards f pX pY hf).obj (squareZeroCrossUnder.{u, u, u}
    ((schemeMorphismDeformationCategoryProjection f pX pY hf).obj
      (schemeMorphismTrivialObject f pX pY hf)) N)).1

/-- The trivial lift over `k[N]`: the arrow of the trivial deformation of `f` over `k[N]`, read as
a lift of `f` to the trivial deformations of its endpoints. -/
def schemeMorphismTrivialLiftAt :
    globalLiftsOverBase f (schemeMorphismSourceTrivialAt f pX pY hf N)
      (schemeMorphismTargetTrivialAt f pX pY hf N)
      (eqToHom ((schemeMorphismTargetTrivialAt_base f pX pY hf N).trans
        (schemeMorphismSourceTrivialAt_base f pX pY hf N).symm)) :=
  schemeMorphismEndpointsLift f pX pY hf (schemeMorphismTrivialFirstOrderAt f pX pY hf N) _

/-- At the rank-one module the trivial lift over `k[N]` is the trivial lift. -/
theorem schemeMorphismTrivialLiftAt_rankOne :
    schemeMorphismTrivialLiftAt f pX pY hf (FGModuleCat.of k (ULift.{u} k)) =
      schemeMorphismTrivialLift f pX pY hf := rfl

/-- The trivial lift over `k[N]` has class zero. -/
theorem liftClass_schemeMorphismTrivialLiftAt
    (hM : IsDeformationCategory.{u, u, u}
      (schemeMorphismDeformationCategoryProjection f pX pY hf)) :
    liftClass f pX pY hf hM N (schemeMorphismTargetTrivialAt_base f pX pY hf N)
      (schemeMorphismTrivialLiftAt f pX pY hf N) = 0 :=
  liftClass_schemeMorphismEndpointsLift_trivial f pX pY hf hM N _ rfl _ _

/-- The trivial lifts are compatible with the maps of coordinate modules: for `φ : M ⟶ N`, the
chosen arrows of the trivial deformations of `X` and of `Y` over `k[φ]` carry the trivial lift
over `k[N]` to the trivial lift over `k[M]`. -/
theorem schemeMorphismTrivialLiftAt_comp_map {M : FGModuleCat.{u} k} (φ : M ⟶ N) :
    (schemeMorphismTrivialLiftAt f pX pY hf N).1 ≫
        ((schemeMorphismTargetPushforwards f pX pY hf).map
          (squareZeroCrossUnderMap.{u, u, u} _ φ)).map =
      ((schemeMorphismSourcePushforwards f pX pY hf).map
          (squareZeroCrossUnderMap.{u, u, u} _ φ)).map ≫
        (schemeMorphismTrivialLiftAt f pX pY hf M).1 := by
  have hX := ChosenPushforwardsAt.ofComp_map (schemeMorphismSourceForgetful f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
    (schemeMorphismTrivialPushforwards f pX pY hf) (squareZeroCrossUnderMap.{u, u, u} _ φ)
  have hY := ChosenPushforwardsAt.ofComp_map (schemeMorphismTargetForgetful f pX pY hf)
    (schemeDeformationCategoryProjection_cofiberedInGroupoids _)
    (schemeMorphismTrivialPushforwards f pX pY hf) (squareZeroCrossUnderMap.{u, u, u} _ φ)
  have hX' : ((schemeMorphismSourcePushforwards f pX pY hf).map
      (squareZeroCrossUnderMap.{u, u, u} _ φ)).map =
        ((schemeMorphismTrivialPushforwards f pX pY hf).map
          (squareZeroCrossUnderMap.{u, u, u} _ φ)).left.source :=
    congrArg SchemeDeformationCategory.Hom.map hX
  have hY' : ((schemeMorphismTargetPushforwards f pX pY hf).map
      (squareZeroCrossUnderMap.{u, u, u} _ φ)).map =
        ((schemeMorphismTrivialPushforwards f pX pY hf).map
          (squareZeroCrossUnderMap.{u, u, u} _ φ)).left.target :=
    congrArg SchemeDeformationCategory.Hom.map hY
  rw [hX', hY']
  exact ((schemeMorphismTrivialPushforwards f pX pY hf).map
    (squareZeroCrossUnderMap.{u, u, u} _ φ)).left.source_pullback.w

end CoordinateModule

end Examples

end Deformation
