module

public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Preadditive.Injective.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactness
public import StacksFrontier.CategoryTheory.Sites.Continuous
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cohomology
public import StacksFrontier.Topology.Simplicial.ComponentSite

/-!
# Extension of sheaves from a component of a simplicial space

For a simplicial topological space, restriction of sheaves from its total site to one of its
degrees has a left adjoint, the lower-shriek functor. This file constructs that left adjoint for
sheaves of sets and for sheaves of abelian groups, shows that the set-valued one commutes with
finite connected limits, shows that the abelian one is exact, and deduces that restriction
carries injective abelian sheaves to injective abelian sheaves.

## Main definitions

* `Stacks.Topology.Simplicial.componentLowerShriek`: lower shriek on sheaves of sets.
* `Stacks.Topology.Simplicial.componentLowerShriekAb`: lower shriek on sheaves of abelian
  groups.

## Main results

* `Stacks.Topology.Simplicial.componentLowerShriek_adjunction` and
  `componentLowerShriekAb_adjunction`: the two adjunctions.
* `Stacks.Topology.Simplicial.componentLowerShriek_preservesFiniteConnectedLimits`: lower shriek
  on sheaves of sets preserves limits of every finite connected shape.
* `Stacks.Topology.Simplicial.componentLowerShriekAb_exact` and
  `Stacks.Topology.Simplicial.exactFunctor_componentLowerShriekAb`: lower shriek on sheaves of
  abelian groups is exact, in a general coefficient universe and, hypothesis-free, for the
  functor `componentLowerShriekAb` itself.
* `Stacks.Topology.Simplicial.componentRestrictionAb_preservesInjectiveObjects` and
  `Stacks.Topology.Simplicial.injective_component`: restriction to a degree preserves injective
  abelian sheaves.

## Implementation notes

Lower shriek is sheafification of left Kan extension along the opposite of the inclusion of the
component site. For sheaves of sets, the right adjoint is represented by the cocontinuous sheaf
pullback along that inclusion, which is identified with restriction to the component by
`Stacks.Topology.Simplicial.inverseImageIsoComponent`; for sheaves of abelian groups, the right
adjoint is the continuous pushforward and the requisite sheafification comes from Stacks 09VV.

Exactness is expressed by preservation of finite limits and finite colimits, both supplied by
Stacks 04BH. Its left-exactness half needs pointwise left Kan extensions; those are produced
from plain left Kan extensions here, using that the hom-sets of the simplicial-open category are
finite, so that products indexed by them exist in abelian groups of any universe. The
coefficient universe is therefore independent of the simplicial-space universe, subject only to
existence of sheafification and of the Kan extensions used to construct lower shriek.

Injectivity of a restriction is read off from the adjunction: the exact left adjoint preserves
monomorphisms, so its right adjoint preserves injective objects. The degree-`n` component of an
abelian sheaf, in the sense of the sheaf-system description of Stacks 09VM, is identified with
that restriction, so the conclusion also holds in the form the source states it.

## References

* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
* [Stacks Project, Tag 09W1](https://stacks.math.columbia.edu/tag/09W1)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits
open CategoryTheory.Functor

universe uC vC uD vD uE vE u w

namespace Stacks.Topology.Simplicial

/-- The lower-shriek functor from sheaves of sets on one component to sheaves of sets on the
simplicial site. -/
@[stacks 09W0 "sheaf_left_adjoint"]
noncomputable def componentLowerShriek
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) (Type u) ⥤
      Sheaf (SimplicialOpen.grothendieckTopology X) (Type u) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (levelFunctor X (op (SimplexCategory.mk n))) (Type u)
    (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    (SimplicialOpen.grothendieckTopology X)

/-- **Stacks 09W0.** Lower shriek is left adjoint to inverse image from the total
simplicial site to a component. -/
@[stacks 09W0 "sheaf_left_adjoint"]
noncomputable def componentLowerShriek_adjunction
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    componentLowerShriek X n ⊣
      (levelFunctor X (op (SimplexCategory.mk n))).sheafPullbackCocontinuous
        (Type u) (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X) :=
  (Functor.sheafAdjunctionLowerShriek _ _ _ _).ofNatIsoRight
    (Functor.sheafPullbackCocontinuousIsoSheafPushforwardContinuous _ _ _ _).symm

/-- **Stacks 09W0.** Lower shriek from a simplicial component preserves finite
connected limits. -/
@[stacks 09W0 "sheaf_left_adjoint_connected_limits"]
theorem componentLowerShriek_preservesFiniteConnectedLimits
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    (J : Type vC) [SmallCategory J] [FinCategory J] [IsConnected J] :
    PreservesLimitsOfShape J (componentLowerShriek X n) := by
  let F := levelFunctor X (op (SimplexCategory.mk n))
  let := Functor.preservesLimitsOfShape_sheafPullback F
    (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    (SimplicialOpen.grothendieckTopology X) (I := J)
  exact preservesLimitsOfShape_of_natIso
    (Functor.sheafPullbackConstruction.sheafPullbackIso F (Type u) _ _)

/-- Lower shriek from sheaves of abelian groups on a component to sheaves of abelian groups on
the total simplicial site. -/
@[stacks 09W0 "abelian_left_adjoint"]
noncomputable def componentLowerShriekAb
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{u} ⥤
      Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u} := by
  letI : HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{u} :=
    Stacks.CategoryTheory.Hypercovering.hasSheafify_addCommGrpCat.{u} _
  exact Functor.sheafPullbackConstruction.sheafPullback
    (levelFunctor X (op (SimplexCategory.mk n))) Ab.{u}
    (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    (SimplicialOpen.grothendieckTopology X)

/-- **Stacks 09W0.** Abelian lower shriek is left adjoint to restriction from
the total simplicial site to a component. -/
@[stacks 09W0 "abelian_left_adjoint"]
noncomputable def componentLowerShriekAb_adjunction
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    componentLowerShriekAb X n ⊣
      (levelFunctor X (op (SimplexCategory.mk n))).sheafPushforwardContinuous
        Ab.{u}
        (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

private theorem hasPointwiseLeftKanExtension_of_hasAllLeftKanExtensions
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
    {E : Type uE} [Category.{vE} E]
    (L : C ⥤ D) [∀ F : C ⥤ E, L.HasLeftKanExtension F]
    [∀ a b : D, CategoryTheory.Limits.HasProductsOfShape.{vD, uE, vE} (a ⟶ b) E]
    (F : C ⥤ E) : L.HasPointwiseLeftKanExtension F := by
  intro Y
  let E₀ : LeftExtension L F :=
    LeftExtension.mk (L.leftKanExtension F) (L.leftKanExtensionUnit F)
  let Dgm := CostructuredArrow.proj L Y ⋙ F
  let c : Cocone Dgm := E₀.coconeAt Y
  let α (s : Cocone Dgm) : F ⟶ L ⋙ (evaluationRightAdjoint E Y).obj s.pt :=
    { app := fun a => by
        dsimp [evaluationRightAdjoint]
        refine Pi.lift fun f => ?_
        let j := CostructuredArrow.mk (Y := a) f
        have hobj : Dgm.obj j = F.obj a := rfl
        exact eqToHom hobj.symm ≫ s.ι.app j
      naturality := by
        intro a b f
        apply Pi.hom_ext
        intro g
        let j₁ : CostructuredArrow L Y := CostructuredArrow.mk (Y := a) (L.map f ≫ g)
        let j₂ : CostructuredArrow L Y := CostructuredArrow.mk (Y := b) g
        simpa [evaluationRightAdjoint, Dgm, CostructuredArrow.proj_obj,
          CostructuredArrow.mk, CostructuredArrow.homMk, j₁, j₂, Category.assoc] using
          s.w (CostructuredArrow.homMk (f := j₁) (f' := j₂) f (by simp [j₁, j₂])) }
  let β (s : Cocone Dgm) := (L.leftKanExtension F).descOfIsLeftKanExtension
    (L.leftKanExtensionUnit F) ((evaluationRightAdjoint E Y).obj s.pt) (α s)
  let d (s : Cocone Dgm) := (β s).app Y ≫
    (evaluationAdjunctionLeft E Y).counit.app s.pt
  have hc : IsColimit c := by
    refine { desc := d, fac := ?_, uniq := ?_ }
    · intro s j
      change ((L.leftKanExtensionUnit F).app j.left ≫
        (L.leftKanExtension F).map j.hom) ≫ (β s).app Y ≫
          (evaluationAdjunctionLeft E Y).counit.app s.pt = s.ι.app j
      rw [Category.assoc, (β s).naturality_assoc j.hom
        ((evaluationAdjunctionLeft E Y).counit.app s.pt)]
      simp only [← Category.assoc]
      rw [(L.leftKanExtension F).descOfIsLeftKanExtension_fac_app
        (L.leftKanExtensionUnit F) ((evaluationRightAdjoint E Y).obj s.pt) (α s) j.left]
      simp [α, evaluationRightAdjoint, evaluationAdjunctionLeft_counit_app]
      rfl
    · intro s f hf
      let β' : L.leftKanExtension F ⟶ (evaluationRightAdjoint E Y).obj s.pt :=
        { app := fun Z => Pi.lift fun g => (L.leftKanExtension F).map g ≫ f
          naturality := by
            intro Z Z' h
            apply Pi.hom_ext
            intro g
            simp [evaluationRightAdjoint, Category.assoc] }
      have hβ : β s = β' := by
        apply (L.leftKanExtension F).hom_ext_of_isLeftKanExtension
          (L.leftKanExtensionUnit F)
        ext a
        apply Pi.hom_ext
        intro g
        dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app]
        change ((L.leftKanExtensionUnit F).app a ≫ (β s).app (L.obj a)) ≫ Pi.π _ g =
          ((L.leftKanExtensionUnit F).app a ≫ β'.app (L.obj a)) ≫ Pi.π _ g
        calc
          ((L.leftKanExtensionUnit F).app a ≫ (β s).app (L.obj a)) ≫ Pi.π _ g =
              s.ι.app (CostructuredArrow.mk (Y := a) g) := by
            rw [(L.leftKanExtension F).descOfIsLeftKanExtension_fac_app
              (L.leftKanExtensionUnit F) ((evaluationRightAdjoint E Y).obj s.pt) (α s) a]
            simp [α, evaluationRightAdjoint]
        _ = ((L.leftKanExtensionUnit F).app a ≫ β'.app (L.obj a)) ≫ Pi.π _ g := by
          rw [← hf (CostructuredArrow.mk (Y := a) g)]
          simp [β', c, E₀, Dgm, evaluationRightAdjoint, Category.assoc]
      change f = d s
      dsimp [d]
      rw [hβ]
      simp [β', evaluationRightAdjoint, evaluationAdjunctionLeft_counit_app]
  exact HasColimit.mk ⟨c, hc⟩

/-- Hom-sets in the opposite of a category are finite when the reversed hom-sets are. -/
private theorem finite_hom_op {C : Type*} [Category C] (a b : Cᵒᵖ) [Finite (b.unop ⟶ a.unop)] :
    Finite (a ⟶ b) :=
  Finite.of_injective (fun f => Opposite.unop f) Opposite.unop_injective

private theorem finiteSimplicialOpenHom (X : SimplicialObject TopCat.{u})
    (U V : SimplicialOpen X) : Finite (U ⟶ V) := by
  have : Finite (U.degree ⟶ V.degree) := finite_hom_op U.degree V.degree
  exact Finite.of_injective SimplicialOpen.Hom.base
    (fun f g h => SimplicialOpen.Hom.ext f g h)

/-- **Stacks 09W0.** Abelian lower shriek from a component of a simplicial space is exact. -/
@[stacks 09W0 "abelian_left_adjoint_exact"]
theorem componentLowerShriekAb_exact
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
      (levelFunctor X (op (SimplexCategory.mk n))).op.HasLeftKanExtension F]
    [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}] :
    exactFunctor
      (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w})
      (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w})
      (Functor.sheafPullbackConstruction.sheafPullback
        (levelFunctor X (op (SimplexCategory.mk n))) Ab.{w}
        (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X)) := by
  let : ∀ a b : (SimplicialOpen X)ᵒᵖ, HasProductsOfShape (a ⟶ b) Ab.{w} := by
    intro a b
    let : Finite (b.unop ⟶ a.unop) := finiteSimplicialOpenHom X b.unop a.unop
    let : Finite (a ⟶ b) := finite_hom_op a b
    infer_instance
  let : ∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
      (levelFunctor X (op (SimplexCategory.mk n))).op.HasPointwiseLeftKanExtension F :=
    fun F => hasPointwiseLeftKanExtension_of_hasAllLeftKanExtensions _ F
  exact (exactFunctor_iff _).2
    ⟨Stacks.Sites.LowerShriek.gShriek_preservesFiniteLimits
      (levelFunctor X (op (SimplexCategory.mk n)))
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X),
    Stacks.Sites.LowerShriek.gShriek_preservesFiniteColimits Ab.{w}
      (levelFunctor X (op (SimplexCategory.mk n)))
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X)⟩

/-- **Stacks 09W0**, part (5): `g_{n!}` is exact.  This is `componentLowerShriekAb_exact` for
the registered functor `componentLowerShriekAb` and with no hypotheses: on the small site of
opens of a topological space, with coefficients in abelian groups of the same universe, both
the left Kan extensions and the sheafification used to build lower shriek exist. -/
@[stacks 09W0 "abelian_left_adjoint_exact"]
theorem exactFunctor_componentLowerShriekAb (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    exactFunctor
      (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{u})
      (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{u})
      (componentLowerShriekAb X n) := by
  let : HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{u} :=
    Stacks.CategoryTheory.Hypercovering.hasSheafify_addCommGrpCat.{u} _
  exact componentLowerShriekAb_exact.{u, u} X n

/-- **Stacks 09W1.** Restriction of abelian sheaves from the site of a simplicial space to the
site of one of its degrees preserves injective objects: it is right adjoint to lower shriek,
which is exact. -/
@[stacks 09W1 "restriction to a degree preserves injectives"]
theorem componentRestrictionAb_preservesInjectiveObjects
    (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
      (levelFunctor X (op (SimplexCategory.mk n))).op.HasLeftKanExtension F]
    [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w}] :
    ((levelFunctor X (op (SimplexCategory.mk n))).sheafPushforwardContinuous Ab.{w}
        (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X)).PreservesInjectiveObjects := by
  obtain ⟨h₁, h₂⟩ := (exactFunctor_iff _).1 (componentLowerShriekAb_exact.{u, w} X n)
  have adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (levelFunctor X (op (SimplexCategory.mk n))) Ab.{w}
    (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
    (SimplicialOpen.grothendieckTopology X)
  have := adj.rightAdjoint_preservesLimits
  have := adj.isLeftAdjoint
  have : HasBinaryProducts Ab.{w} := inferInstance
  have : HasBinaryProducts ((SimplicialOpen X)ᵒᵖ ⥤ Ab.{w}) := inferInstance
  have : HasBinaryProducts
      ((Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w}) := inferInstance
  have : HasBinaryProducts (Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :=
    inferInstance
  have : HasBinaryProducts
      (Sheaf (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w}) :=
    inferInstance
  have := Functor.additive_of_preserves_binary_products
    ((levelFunctor X (op (SimplexCategory.mk n))).sheafPushforwardContinuous Ab.{w}
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X))
  have := Functor.additive_of_preserves_binary_products
    (Functor.sheafPullbackConstruction.sheafPullback
      (levelFunctor X (op (SimplexCategory.mk n))) Ab.{w}
      (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
      (SimplicialOpen.grothendieckTopology X))
  exact (preservesInjectiveObjects_of_exact_of_adjunction _ _ adj).2 ⟨h₁, h₂⟩

/-- The degree-`n` component of an abelian sheaf on the site of a simplicial space is its
restriction along the inclusion of the site of that degree. -/
private noncomputable def pushforwardObjIsoComponent (X : SimplicialObject TopCat.{u}) (n : ℕ)
    (E : SheafSystemEquivalence X Ab.{w})
    (I : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) :
    ((levelFunctor X (op (SimplexCategory.mk n))).sheafPushforwardContinuous Ab.{w}
        (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
        (SimplicialOpen.grothendieckTopology X)).obj I ≅
      (E.toEquivalence.functor.obj I).component (op (SimplexCategory.mk n)) :=
  (fullyFaithfulSheafToPresheaf _ Ab.{w}).preimageIso
    ((Functor.sheafPushforwardContinuousCompSheafToPresheafIso
          (levelFunctor X (op (SimplexCategory.mk n))) Ab.{w}
          (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n))))
          (SimplicialOpen.grothendieckTopology X)).app I ≪≫
      ((componentPresheafFunctor X Ab.{w} (op (SimplexCategory.mk n))).mapIso
          (E.underlyingPresheafIso.app I)).symm ≪≫
      (E.componentIso (op (SimplexCategory.mk n))).app (E.toEquivalence.functor.obj I))

/-- **Stacks 09W1.** If `I` is an injective abelian sheaf on the site of a simplicial space `X`,
then its degree-`n` component `I n` is an injective abelian sheaf on `X n`. -/
@[stacks 09W1]
theorem injective_component (X : SimplicialObject TopCat.{u}) (n : ℕ)
    [∀ F : (Opens (X.obj (op (SimplexCategory.mk n))))ᵒᵖ ⥤ Ab.{w},
      (levelFunctor X (op (SimplexCategory.mk n))).op.HasLeftKanExtension F]
    [HasSheafify (SimplicialOpen.grothendieckTopology X) Ab.{w}]
    [HasSheafify (Opens.grothendieckTopology (X.obj (op (SimplexCategory.mk n)))) Ab.{w}]
    (E : SheafSystemEquivalence X Ab.{w})
    (I : Sheaf (SimplicialOpen.grothendieckTopology X) Ab.{w}) [Injective I] :
    Injective ((E.toEquivalence.functor.obj I).component (op (SimplexCategory.mk n))) :=
  Injective.of_iso (pushforwardObjIsoComponent X n E I)
    ((componentRestrictionAb_preservesInjectiveObjects X n).injective_obj
      (inferInstanceAs (Injective I)))

end Stacks.Topology.Simplicial

end
