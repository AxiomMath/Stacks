module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberSquareRestrictionEquivalence

/-!
# The comparison functor of a square, with the chosen pullbacks or with the base changes

For a fibred category `p : 𝒳 ⥤ 𝒮` and a commutative square `f ≫ i = g ≫ j` of `𝒮`, two
comparison functors from the fibre over the fourth corner to a `2`-fibre product of fibres are in
use: `Deformation.Artin.fiberSquareComparison`, built from a choice of pullbacks — the one
condition (RS*) of Stacks 07Y8 is phrased with — and
`CategoryTheory.Functor.fiberSquareRestriction`, built from the base-change functors
`CategoryTheory.Functor.fiberPullback`, for which
`CategoryTheory.Functor.isEquivalence_fiberSquareRestriction` gives a criterion in terms of
arbitrary cartesian morphisms.  This file shows that, for the canonical choice of pullbacks
`CategoryTheory.Functor.chosenPullbacks`, the first is an equivalence as soon as the second is.

## Main results

* `CategoryTheory.Functor.chosenPullbackFunctorIso`: the chosen pullback functor is the
  base-change functor on fibres.
* `Functor.isEquivalence_fiberSquareComparison_of_isEquivalence_fiberSquareRestriction`: the
  transfer of the equivalence property.
* `CategoryTheory.Functor.isEquivalence_fiberSquareComparison_of_glue`: the gluing criterion of
  `CategoryTheory.Functor.isEquivalence_fiberSquareRestriction`, read for the comparison functor
  of condition (RS*).

## Implementation notes

The argument is the one of `Functor.isEquivalence_fiberSquareComparison_sliceAtTerminal` with
the slice functors replaced by identities: the two comparison functors differ by the functor of
`2`-fibre products induced by the identifications of the pullback functors, which is an
equivalence by Stacks 02XB, and the coherence of the two structure isomorphisms is checked after
composing with a cartesian morphism.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Functor.fiberPullback

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {𝒳 : Type u₂} [Category.{v₂} 𝒳] (p : 𝒳 ⥤ C)
  [p.IsFibered]

/-- **The chosen pullback functor is the base-change functor on fibres.**  Both send an object
of the fibre over `A'` to the domain of a cartesian lift of `g`; the comparison is the canonical
isomorphism between two such domains. -/
def chosenPullbackFunctorIso {A A' : C} (g : A ⟶ A') :
    (chosenPullbacks p).pullbackFunctor g ≅ fiberPullback p g :=
  NatIso.ofComponents
    (fun y => fiberIsoOfCartesian g ((chosenPullbacks p).map g y) (fiberPullbackHom p g y)
      (inferInstanceAs (p.IsCartesian g (fiberPullbackHom p g y)))
      (isCartesian_fiberPullbackHom p g y))
    (fun {y y'} α => by
      refine fiber_hom_ext_of_cartesian g (fiberPullbackHom p g y')
        (isCartesian_fiberPullbackHom p g y') _ _ ?_
      simp only [Functor.map_comp, Category.assoc]
      rw [fiberIsoOfCartesian_hom_fac, fiberPullback_map_fac, fiberIsoOfCartesian_hom_fac_assoc]
      exact (chosenPullbacks p).homMap_fac g α)

/-- The comparison of the chosen pullback with the base change commutes with the cartesian
morphisms. -/
@[reassoc (attr := simp)]
theorem chosenPullbackFunctorIso_hom_app_fac {A A' : C} (g : A ⟶ A') (y : p.Fiber A') :
    Fiber.fiberInclusion.map ((chosenPullbackFunctorIso p g).hom.app y) ≫
        fiberPullbackHom p g y = (chosenPullbacks p).map g y :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse comparison of the chosen pullback with the base change commutes with the
cartesian morphisms. -/
@[reassoc (attr := simp)]
theorem chosenPullbackFunctorIso_inv_app_fac {A A' : C} (g : A ⟶ A') (y : p.Fiber A') :
    Fiber.fiberInclusion.map ((chosenPullbackFunctorIso p g).inv.app y) ≫
        (chosenPullbacks p).map g y = fiberPullbackHom p g y :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

section Square

variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)

attribute [local implicit_reducible] CategoryTheory.Functor.fiberSquareRestriction
  CategoryTheory.Limits.CategoricalPullback.map
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback

/-- The coherence of the two structure isomorphisms of the comparison functors, in explicit
form. -/
theorem fiberSquareComparison_restriction_coherence (z : p.Fiber Z) :
    (fiberPullback p f).map ((chosenPullbackFunctorIso p i).hom.app z) ≫
        (fiberPullbackSquareIso p g f j i h).hom.app z =
      ((chosenPullbackFunctorIso p f).inv.app ((chosenPullbacks p).obj i z) ≫
        (((chosenPullbacks p).pullbackFunctorCompIso f i).symm ≪≫
            eqToIso (congrArg (chosenPullbacks p).pullbackFunctor h) ≪≫
            (chosenPullbacks p).pullbackFunctorCompIso g j).hom.app z ≫
        (chosenPullbackFunctorIso p g).hom.app ((chosenPullbacks p).obj j z)) ≫
        (fiberPullback p g).map ((chosenPullbackFunctorIso p j).hom.app z) := by
  refine fiber_hom_ext_of_cartesian (g ≫ j)
    (fiberPullbackHom p g ((fiberPullback p j).obj z) ≫ fiberPullbackHom p j z)
    (isCartesian_fiberPullbackHom_comp p g j _) _ _ ?_
  simp only [fiberPullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, Functor.comp_obj, fiberPullbackCompIso_inv_app_fac,
    fiberPullback_map_fac_assoc, chosenPullbackFunctorIso_hom_app_fac,
    chosenPullbackFunctorIso_hom_app_fac_assoc,
    choiceOfPullbacks_pullbackFunctorCompIso_hom_app_fac]
  rw [eqToHom_app_fiberPullbackHom p h, eqToHom_app_choiceOfPullbacks_map _ h,
    fiberPullbackCompIso_hom_app_fac, fiberPullback_map_fac_assoc,
    chosenPullbackFunctorIso_hom_app_fac, choiceOfPullbacks_pullbackFunctorCompIso_inv_app_fac]
  exact (chosenPullbackFunctorIso_inv_app_fac_assoc p f ((chosenPullbacks p).obj i z)
    ((chosenPullbacks p).map i z)).symm

/-- **The comparison functor of condition (RS*) is an equivalence as soon as the comparison
functor of base changes is.**  For a commutative square `f ≫ i = g ≫ j` of the base of a fibred
category, the comparison `Deformation.Artin.fiberSquareComparison` built from the canonical
choice of pullbacks is an equivalence if `CategoryTheory.Functor.fiberSquareRestriction` is. -/
theorem isEquivalence_fiberSquareComparison_of_isEquivalence_fiberSquareRestriction
    (hres : (fiberSquareRestriction p g f j i h).IsEquivalence) :
    (Deformation.Artin.fiberSquareComparison p (chosenPullbacks p) f g i j h).IsEquivalence := by
  let Φ := CategoricalPullback.map ((chosenPullbacks p).pullbackFunctor f)
    ((chosenPullbacks p).pullbackFunctor g) (𝟭 (p.Fiber V)) (𝟭 (p.Fiber W)) (𝟭 (p.Fiber U))
    (fiberPullback p f) (fiberPullback p g)
    (chosenPullbackFunctorIso p g).symm (chosenPullbackFunctorIso p f)
  have : Φ.IsEquivalence :=
    induced_isEquivalence_of_isEquivalence (𝟭 (p.Fiber V)) (𝟭 (p.Fiber W)) (𝟭 (p.Fiber U)) _ _
  let θ : Deformation.Artin.fiberSquareComparison p (chosenPullbacks p) f g i j h ⋙ Φ ≅
      fiberSquareRestriction p g f j i h :=
    NatIso.ofComponents
      (fun z => CategoricalPullback.mkIso ((chosenPullbackFunctorIso p i).app z)
        ((chosenPullbackFunctorIso p j).app z)
        (by
          simp only [Φ, Functor.comp_obj, CategoricalPullback.map_obj_iso_hom]
          refine (fiberSquareComparison_restriction_coherence p f g i j h z).trans ?_
          simp only [Iso.symm_inv, Iso.app_hom, Functor.id_map]
          dsimp only [Deformation.Artin.fiberSquareComparison,
            CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback]
          simp only [Iso.app_hom]
          rfl))
      (fun {z z'} φ => CategoricalPullback.hom_ext
        ((chosenPullbackFunctorIso p i).hom.naturality φ)
        ((chosenPullbackFunctorIso p j).hom.naturality φ))
  have := Functor.isEquivalence_of_iso θ.symm
  exact Functor.isEquivalence_of_comp_right _ Φ

/-- **The gluing criterion for the comparison functor of condition (RS*).**  The comparison
`Deformation.Artin.fiberSquareComparison` of a commutative square `f ≫ i = g ≫ j`, built from the
canonical choice of pullbacks, is an equivalence as soon as morphisms and objects glue along the
square, in the sense of `CategoryTheory.Functor.isEquivalence_fiberSquareRestriction`. -/
theorem isEquivalence_fiberSquareComparison_of_glue
    (hFF : ∀ a : p.Fiber Z, ∃ (aV aW aU : 𝒳) (c : aV ⟶ Fiber.fiberInclusion.obj a)
      (d : aW ⟶ Fiber.fiberInclusion.obj a) (u : aU ⟶ aV) (v : aU ⟶ aW),
      p.IsCartesian i c ∧ p.IsCartesian j d ∧ p.IsHomLift f u ∧ p.IsHomLift g v ∧
        u ≫ c = v ≫ d ∧
        ∀ (b : p.Fiber Z) (α : aV ⟶ Fiber.fiberInclusion.obj b)
          (β : aW ⟶ Fiber.fiberInclusion.obj b), p.IsHomLift i α → p.IsHomLift j β →
          u ≫ α = v ≫ β →
          ∃! φ : a ⟶ b, c ≫ Fiber.fiberInclusion.map φ = α ∧
            d ≫ Fiber.fiberInclusion.map φ = β)
    (hES : ∀ (xV : p.Fiber V) (xW : p.Fiber W) (xU : 𝒳)
      (u : xU ⟶ Fiber.fiberInclusion.obj xV) (v : xU ⟶ Fiber.fiberInclusion.obj xW),
      p.IsCartesian f u → p.IsCartesian g v →
      ∃ (a : p.Fiber Z) (μ : Fiber.fiberInclusion.obj xV ⟶ Fiber.fiberInclusion.obj a)
        (ν : Fiber.fiberInclusion.obj xW ⟶ Fiber.fiberInclusion.obj a),
        p.IsCartesian i μ ∧ p.IsCartesian j ν ∧ u ≫ μ = v ≫ ν) :
    (Deformation.Artin.fiberSquareComparison p (chosenPullbacks p) f g i j h).IsEquivalence :=
  isEquivalence_fiberSquareComparison_of_isEquivalence_fiberSquareRestriction p f g i j h
    (isEquivalence_fiberSquareRestriction p g f j i h hFF hES)

end Square

end CategoryTheory.Functor

end
