module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionLimitPreserving
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence

/-!
# Completion commutes with the change of base of Stacks 04SG

Let `g : V ⟶ S` be a morphism of a big fppf site, let `X` be an algebraic space over `S` with a
morphism to the representable presheaf of `g`, let `X_V` be the algebraic space over `V` that
Stacks 04SG attaches to it, and let `T ⊆ |X|`, with inverse image `T_V ⊆ |X_V|` under the
homeomorphism `AlgebraicGeometry.Space.pointsSmallerBaseInverseHomeomorph`. This file shows that
the completion `X_{V,/T_V}` of Stacks 0AMC, an fppf sheaf of `Type (u + 1)` on the big fppf site of
`V`, corresponds under the equivalence
`AlgebraicGeometry.FormalSpace.smallerBaseSheafEquivalence` to the completion `X_{/T}` over `S`,
equipped with its morphism `X_{/T} ⟶ X ⟶ h_V`.

## Main definitions

* `AlgebraicGeometry.Space.completionSubfunctorSmallerBaseIso`: the identification, at the level
  of the subfunctors of sections with point-set image in the given sets, of the large-valued
  coproduct presheaf of the completion over `V` with the completion over `S`.
* `AlgebraicGeometry.Space.completionSheafToSmallerBase`: the morphism `X_{/T} ⟶ X ⟶ h_V`.
* `AlgebraicGeometry.Space.completionSheafSmallerBaseIso`: **completion commutes with the change of
  base**: the image of `X_{V,/T_V}` under
  `AlgebraicGeometry.FormalSpace.smallerBaseSheafEquivalence` is `X_{/T}` over `h_V`.

## Main results

* `AlgebraicGeometry.Space.hasImageIn_smallerBaseInverseRelocalizeEquiv_iff`: the two point-set
  conditions match.
* `AlgebraicGeometry.Space.completionSubfunctorToSmallerBase_completionSubfunctorSmallerBaseEquiv`:
  the identification is one over `h_V`.

## Implementation notes

Both completions are subfunctors of sections with point-set image in the given set, without any
sheafification, because `X` and `X_V` are fppf sheaves
(`AlgebraicGeometry.Space.completionSheafIsoSubfunctor`). A section of the coproduct presheaf of
the completion over `V` is a factorization `φ : W ⟶ V` of the structure morphism of `W ⟶ S`
together with a section of `X_V` over `(W, φ)` with point-set image in `T_V`; the bijection
`AlgebraicGeometry.Space.smallerBaseInverseRelocalizeEquiv` turns it into a section of `X` over
`W`, and `AlgebraicGeometry.Space.hasImageIn_smallerBaseInverse_iff` matches the two point-set
conditions.

## References

* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0AMC](https://stacks.math.columbia.edu/tag/0AMC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)
  (X : Over (yoneda.obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
  (T : Set (points B S hS X.left))

/-- The presheaf `X_V` on the big fppf site of `V` that Stacks 04SG attaches to `X`. -/
noncomputable abbrev smallerBaseInverse : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u :=
  (smallerBasePresheafEquivalence B V S hV hS g).inverse.obj X

/-- The inverse image `T_V ⊆ |X_V|` of `T ⊆ |X|`. -/
abbrev smallerBaseInverseSet : Set (points B V hV (smallerBaseInverse B V S hV hS g X)) :=
  pointsSmallerBaseInverseHomeomorph B V S hV hS g X ⁻¹' T

/-- Having point-set image in `T` is invariant under restriction along an isomorphism of the big
fppf site of `S`. -/
theorem hasImageIn_map_iff_of_isIso {W W' : BigFppfOver B S hS} (f : W' ⟶ W) [IsIso f]
    (y : X.left.obj (op W)) :
    HasImageIn B S hS X.left T W' (X.left.map f.op y) ↔ HasImageIn B S hS X.left T W y := by
  refine ⟨fun h => ?_, fun h => (completionSubfunctor B S hS X.left T).map f.op
    (a := ULift.up y) h⟩
  have := (completionSubfunctor B S hS X.left T).map (inv f).op
    (a := ULift.up (X.left.map f.op y)) h
  change HasImageIn B S hS X.left T W (X.left.map (inv f).op (X.left.map f.op y)) at this
  rwa [← FunctorToTypes.map_comp_apply, ← op_comp, IsIso.inv_hom_id, op_id,
    FunctorToTypes.map_id_apply] at this

/-- For `ψ : W ⟶ V` with `ψ ≫ g = W.hom`, the morphism
`AlgebraicGeometry.Space.smallerBaseFactorHom` of the big fppf site of `S` is an isomorphism. -/
instance {W : BigFppfOver B S hS} {ψ : W.left ⟶ B.obj hV} (h : ψ ≫ g = W.hom) :
    IsIso (smallerBaseFactorHom B V S hV hS g h) :=
  ⟨smallerBaseFactorHomInv B V S hV hS g h,
    Over.OverMorphism.ext (by simp [smallerBaseFactorHom, smallerBaseFactorHomInv]),
    Over.OverMorphism.ext (by simp [smallerBaseFactorHom, smallerBaseFactorHomInv])⟩

/-- A section of the lower-shriek extension of `X_V` has point-set image in `T_V` over `V` exactly
when the corresponding section of `X` has point-set image in `T` over `S`. -/
theorem hasImageIn_smallerBaseInverseRelocalizeEquiv_iff {W : (BigFppfOver B S hS)ᵒᵖ}
    (y : ((OverShriek.relocalizePresheafFunctor g).obj
      (smallerBaseInverse B V S hV hS g X)).obj W) :
    HasImageIn B V hV _ (smallerBaseInverseSet B V S hV hS g X T) (Over.mk y.1.1) y.1.2 ↔
      HasImageIn B S hS X.left T W.unop
        (smallerBaseInverseRelocalizeEquiv B V S hV hS g X W y) := by
  rw [hasImageIn_smallerBaseInverse_iff]
  exact (hasImageIn_map_iff_of_isIso B V S hV hS g X T
    (smallerBaseFactorHom B V S hV hS g (OverShriek.relocalizeFactors g _ y)) _).symm

/-- The morphism `X_{/T} ⟶ h_V` at the level of subfunctors: a section of `X` with point-set image
in `T` goes to its image under the structural morphism `X ⟶ h_V`. -/
def completionSubfunctorToSmallerBase :
    (completionSubfunctor B S hS X.left T).toFunctor ⟶ uliftYoneda.{u + 1}.obj (Over.mk g) :=
  (completionSubfunctor B S hS X.left T).ι ≫ Functor.whiskerRight X.hom uliftFunctor.{u + 1}

/-- The completion subfunctor over `S`, viewed over the universe-lifted representable presheaf of
`g` through `AlgebraicGeometry.Space.completionSubfunctorToSmallerBase`. -/
abbrev completionSubfunctorOverSmallerBase : Over (uliftYoneda.{u + 1}.obj (Over.mk g)) :=
  Over.mk (completionSubfunctorToSmallerBase B V S hV hS g X T)

/-- The sections over `W` of the large-valued coproduct presheaf of the completion subfunctor of
`X_V` along `T_V` are the sections of the completion subfunctor of `X` along `T`. -/
noncomputable def completionSubfunctorSmallerBaseEquiv (W : (BigFppfOver B S hS)ᵒᵖ) :
    ((FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
        (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
          (smallerBaseInverseSet B V S hV hS g X T)).toFunctor).left.obj W ≃
      (completionSubfunctor B S hS X.left T).toFunctor.obj W where
  toFun p := ⟨ULift.up (smallerBaseInverseRelocalizeEquiv B V S hV hS g X W
      ⟨⟨p.1.left, p.2.1.down⟩, Over.w p.1⟩),
    (hasImageIn_smallerBaseInverseRelocalizeEquiv_iff B V S hV hS g X T
      ⟨⟨p.1.left, p.2.1.down⟩, Over.w p.1⟩).1 p.2.2⟩
  invFun t :=
    let y := (smallerBaseInverseRelocalizeEquiv B V S hV hS g X W).symm t.1.down
    ⟨Over.homMk y.1.1 (OverShriek.relocalizeFactors g _ y), ⟨ULift.up y.1.2, by
      have := (hasImageIn_smallerBaseInverseRelocalizeEquiv_iff B V S hV hS g X T y).2
      rw [Equiv.apply_symm_apply] at this
      exact this t.2⟩⟩
  left_inv := by
    rintro ⟨φ, ⟨x⟩, hx⟩
    have key := (smallerBaseInverseRelocalizeEquiv B V S hV hS g X W).symm_apply_apply
      ⟨⟨φ.left, x⟩, Over.w φ⟩
    have hmk : ∀ (y y' : ((OverShriek.relocalizePresheafFunctor g).obj
        (smallerBaseInverse B V S hV hS g X)).obj W) (_ : y = y') hy hy',
        (⟨Over.homMk y.1.1 (OverShriek.relocalizeFactors g _ y), ⟨ULift.up y.1.2, hy⟩⟩ :
          ((FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
            (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
              (smallerBaseInverseSet B V S hV hS g X T)).toFunctor).left.obj W) =
        ⟨Over.homMk y'.1.1 (OverShriek.relocalizeFactors g _ y'), ⟨ULift.up y'.1.2, hy'⟩⟩ := by
      rintro y _ rfl _ _
      rfl
    exact (hmk _ _ key _ hx).trans rfl
  right_inv := by
    rintro ⟨⟨t⟩, ht⟩
    exact Subtype.ext <| congrArg ULift.up <|
      (smallerBaseInverseRelocalizeEquiv B V S hV hS g X W).apply_symm_apply t

/-- The bijections `AlgebraicGeometry.Space.completionSubfunctorSmallerBaseEquiv` are natural. -/
theorem completionSubfunctorSmallerBaseEquiv_naturality {W W' : (BigFppfOver B S hS)ᵒᵖ}
    (f : W ⟶ W')
    (p : ((FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
        (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
          (smallerBaseInverseSet B V S hV hS g X T)).toFunctor).left.obj W) :
    completionSubfunctorSmallerBaseEquiv B V S hV hS g X T W'
        (((FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
          (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
            (smallerBaseInverseSet B V S hV hS g X T)).toFunctor).left.map f p) =
      (completionSubfunctor B S hS X.left T).toFunctor.map f
        (completionSubfunctorSmallerBaseEquiv B V S hV hS g X T W p) := by
  obtain ⟨φ, ⟨x⟩, hx⟩ := p
  apply Subtype.ext
  apply ULift.ext
  show X.left.map _ (X.left.map _ x.1) = X.left.map f (X.left.map _ x.1)
  refine (FunctorToTypes.map_comp_apply X.left _ _ x.1).symm.trans
    (Eq.trans ?_ (FunctorToTypes.map_comp_apply X.left _ f x.1))
  refine congrArg (fun k => X.left.map k x.1) (Quiver.Hom.unop_inj ?_)
  refine Over.OverMorphism.ext ?_
  show 𝟙 _ ≫ f.unop.left = f.unop.left ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- The bijections `AlgebraicGeometry.Space.completionSubfunctorSmallerBaseEquiv` are compatible
with the two morphisms to `h_V`: a section of the coproduct presheaf goes to its factorization
`φ : W ⟶ V`, and so does the corresponding section of `X` under the structural morphism. -/
theorem completionSubfunctorToSmallerBase_completionSubfunctorSmallerBaseEquiv
    {W : (BigFppfOver B S hS)ᵒᵖ}
    (p : ((FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
        (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
          (smallerBaseInverseSet B V S hV hS g X T)).toFunctor).left.obj W) :
    (completionSubfunctorToSmallerBase B V S hV hS g X T).app W
        (completionSubfunctorSmallerBaseEquiv B V S hV hS g X T W p) =
      ((FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
        (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
          (smallerBaseInverseSet B V S hV hS g X T)).toFunctor).hom.app W p := by
  obtain ⟨φ, ⟨x⟩, hx⟩ := p
  apply ULift.ext
  show X.hom.app W (X.left.map _ x.1) = φ
  refine (NatTrans.naturality_apply X.hom _ x.1).trans (Over.OverMorphism.ext ?_)
  show 𝟙 _ ≫ (X.hom.app _ x.1).left = φ.left
  rw [Category.id_comp]
  exact congrArg Over.Hom.left x.2

/-- **Completion commutes with the change of base, on subfunctors.** The large-valued presheaf over
`S` that `AlgebraicGeometry.FormalSpace.smallerBasePresheafEquivalenceULift` attaches to the
completion subfunctor of `X_V` along `T_V` is the completion subfunctor of `X` along `T`, together
with its morphism to `h_V`. -/
noncomputable def completionSubfunctorSmallerBaseIso :
    (FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.obj
        (completionSubfunctor B V hV (smallerBaseInverse B V S hV hS g X)
          (smallerBaseInverseSet B V S hV hS g X T)).toFunctor ≅
      completionSubfunctorOverSmallerBase B V S hV hS g X T :=
  Over.isoMk (NatIso.ofComponents
    (fun W => (completionSubfunctorSmallerBaseEquiv B V S hV hS g X T W).toIso)
    (fun f => by
      ext p
      exact completionSubfunctorSmallerBaseEquiv_naturality B V S hV hS g X T f p))
    (by
      ext W p
      exact completionSubfunctorToSmallerBase_completionSubfunctorSmallerBaseEquiv
        B V S hV hS g X T p)

/-- The morphism `X_{/T} ⟶ X ⟶ h_V` from the completion of an algebraic space `X` over `S` along
`T`, when `X` comes with a morphism to the representable presheaf of `g : V ⟶ S`. -/
noncomputable def completionSheafToSmallerBase (hX : IsAlgebraicSpace B S hS X.left) :
    (completionSheaf B S hS X.left T).obj ⟶ uliftYoneda.{u + 1}.obj (Over.mk g) :=
  (completionSheafIsoSubfunctor B S hS hX.isSheaf T).hom ≫
    completionSubfunctorToSmallerBase B V S hV hS g X T

/-- **Completion commutes with the change of base of Stacks 04SG.** Let `X` be an algebraic space
over `S` with a morphism to the representable presheaf of `g : V ⟶ S`, let `X_V` be the algebraic
space over `V` that Stacks 04SG attaches to it, and let `T ⊆ |X|` with inverse image
`T_V ⊆ |X_V|`. The completion `X_{V,/T_V}` of Stacks 0AMC over `V` corresponds, under the
equivalence `AlgebraicGeometry.FormalSpace.smallerBaseSheafEquivalence`, to the completion
`X_{/T}` over `S` with its morphism `X_{/T} ⟶ X ⟶ h_V`. -/
noncomputable def completionSheafSmallerBaseIso (hX : IsAlgebraicSpace B S hS X.left) :
    ((FormalSpace.smallerBaseSheafEquivalence B V S hV hS g).functor.obj
        (completionSheaf B V hV (smallerBaseInverse B V S hV hS g X)
          (smallerBaseInverseSet B V S hV hS g X T))).obj ≅
      Over.mk (completionSheafToSmallerBase B V S hV hS g X T hX) :=
  (FormalSpace.smallerBasePresheafEquivalenceULift B V S hV hS g).functor.mapIso
      (completionSheafIsoSubfunctor B V hV
        (isAlgebraicSpace_smallerBasePresheafEquivalence_inverse B V S hV hS g X hX).isSheaf
        (smallerBaseInverseSet B V S hV hS g X T)) ≪≫
    completionSubfunctorSmallerBaseIso B V S hV hS g X T ≪≫
    Over.isoMk (completionSheafIsoSubfunctor B S hS hX.isSheaf T).symm
      (by simp [completionSheafToSmallerBase])

end AlgebraicGeometry.Space

end
