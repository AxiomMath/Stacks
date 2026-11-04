module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraPullbackMulCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepThree
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleGradedAlgebraPullbackComp

/-!
# Pullback of a sheaf of graded algebras along an étale morphism is restriction

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`.  Stacks' Equation 03LW identifies the pullback `f^*G` of an `𝒪_Y`-module with its
étale restriction `G|_{X_étale}`, whose sections over an étale chart `W` of `X` are the sections
of `G` over the composite chart `W ⟶ X ⟶ Y`; that identification is
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, a natural isomorphism of functors
of sheaves of *modules*.  This file proves that it is **multiplicative**: for a sheaf of graded
`𝒪_Y`-algebras `𝒜` and a sheaf of graded `𝒪_X`-algebras `𝒜'` identified, degree by degree, with
the restrictions of the pieces of `𝒜` compatibly with the multiplications, the degreewise
identifications `f^*𝒜_n ≅ 𝒜_n|_{X_étale} ≅ 𝒜'_n` assemble into an isomorphism of sheaves of
graded algebras `f^*𝒜 ≅ 𝒜'`.

## Main definitions

* `AlgebraicGeometry.Space.etaleGradedPullbackIso`: **the isomorphism of sheaves of graded
  algebras `f^*𝒜 ≅ 𝒜'`** whose degree-`n` component is the identification of Stacks 03LW
  followed by the given comparison of `𝒜_n|_{X_étale}` with `𝒜'_n`.

## Main results

* `AlgebraicGeometry.Space.restriction_mulSheafHom_comp`: the restriction of the multiplication of
  `𝒜`, followed by the comparison, is the multiplication of `𝒜'`, as morphisms of sheaves of sets.
* `AlgebraicGeometry.Space.isInverseImageMultiplicative_etale`: the multiplicativity criterion of
  `Stacks.Sheaves.GradedAlgebraEssentiallySmall.IsInverseImageMultiplicative` holds for the
  degreewise family.

## Implementation notes

The multiplicativity of a family out of a pullback is tested, by
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.homOfInverseImageMultiplicative`, on the
underlying morphisms of sheaves of sets out of the inverse images `f⁻¹𝒜_n`.  For the
identification of Stacks 03LW that underlying morphism is the comparison of Stacks 03LQ between
the inverse image and restriction of sheaves of sets
(`AlgebraicGeometry.Space.pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback`), a
*natural* transformation; so the test is naturality of that comparison at the multiplication of
`𝒜` and at the two projections of a product, followed by a computation on sections of the
restriction, where everything is read at the composite chart.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 0FQX](https://stacks.math.columbia.edu/tag/0FQX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.GradedAlgebraInverseImage
open Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (𝒜 : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O))
    (𝒜' : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS X).O))
    (c : ∀ n : ℤ, (etaleModulePullback.{u, u} B S hS f hf).obj (𝒜.piece n) ≅ 𝒜'.piece n)

/-- **A multiplicativity square transfers along a natural transformation.**  If `G` carries a
morphism `m : P ⨯ Q ⟶ R` to one which, followed by `k_R`, is the pair `(k_P, k_Q)` followed by
`m'`, then the same holds for `F` with `θ ≫ k` in place of `k`, for any `θ : F ⟶ G`. -/
theorem natTrans_comp_mul_transfer {C D : Type*} [Category C] [Category D] [HasBinaryProducts C]
    [HasBinaryProducts D] {F G : C ⥤ D} (θ : F ⟶ G) {P Q R : C} {P' Q' R' : D}
    (m : P ⨯ Q ⟶ R) (m' : P' ⨯ Q' ⟶ R') (kP : G.obj P ⟶ P') (kQ : G.obj Q ⟶ Q')
    (kR : G.obj R ⟶ R')
    (h : G.map m ≫ kR = Limits.prod.lift (G.map Limits.prod.fst ≫ kP)
      (G.map Limits.prod.snd ≫ kQ) ≫ m') :
    F.map m ≫ θ.app R ≫ kR = Limits.prod.lift (F.map Limits.prod.fst ≫ θ.app P ≫ kP)
      (F.map Limits.prod.snd ≫ θ.app Q ≫ kQ) ≫ m' := by
  rw [← Category.assoc, θ.naturality, Category.assoc, h, ← Category.assoc, Limits.prod.comp_lift]
  simp only [NatTrans.naturality_assoc]

/-- **The comparison of the restricted pieces with `𝒜'` is multiplicative**: on sections over an
étale chart `W` of `X`, which are sections of the pieces of `𝒜` over the composite chart, the
comparison carries the multiplication of `𝒜` to the multiplication of `𝒜'`. -/
def IsEtaleRestrictionMultiplicative : Prop :=
  ∀ (i j : ℤ) (W : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (𝒜.piece i).val.obj (op ((smallEtalePostcomp B S hS f hf).obj W.unop)))
    (y : (𝒜.piece j).val.obj (op ((smallEtalePostcomp B S hS f hf).obj W.unop))),
    (c (i + j)).hom.val.app W ((𝒜.mul i j).app _ x y) =
      (𝒜'.mul i j).app W ((c i).hom.val.app W x) ((c j).hom.val.app W y)

variable {B S hS f hf 𝒜 𝒜' c}

/-- **The restriction of the multiplication of `𝒜`, followed by the comparison, is the
multiplication of `𝒜'`**, as morphisms of sheaves of sets on the small étale site of `X` out of
the restriction of the product of two pieces.  Restriction of sheaves of sets is reindexing of
sections along postcomposition, so both sides are read at the composite chart. -/
theorem restriction_mulSheafHom_comp (hc : IsEtaleRestrictionMultiplicative B S hS f hf 𝒜 𝒜' c)
    (i j : ℤ) :
    (smallEtaleSetRestriction B S hS f hf).map (mulSheafHom 𝒜 i j) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c (i + j)).hom =
      Limits.prod.lift
          ((smallEtaleSetRestriction B S hS f hf).map (Limits.prod.fst :
              moduleSetSheaf B S hS Y (𝒜.piece i) ⨯ moduleSetSheaf B S hS Y (𝒜.piece j) ⟶ _) ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c i).hom)
          ((smallEtaleSetRestriction B S hS f hf).map (Limits.prod.snd :
              moduleSetSheaf B S hS Y (𝒜.piece i) ⨯ moduleSetSheaf B S hS Y (𝒜.piece j) ⟶ _) ≫
            (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c j).hom) ≫
        mulSheafHom 𝒜' i j := by
  refine Sheaf.hom_ext_sections fun W z => ?_
  set a := (smallEtaleSetRestriction B S hS f hf).map (Limits.prod.fst :
      moduleSetSheaf B S hS Y (𝒜.piece i) ⨯ moduleSetSheaf B S hS Y (𝒜.piece j) ⟶ _) ≫
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c i).hom
  set b := (smallEtaleSetRestriction B S hS f hf).map (Limits.prod.snd :
      moduleSetSheaf B S hS Y (𝒜.piece i) ⨯ moduleSetSheaf B S hS Y (𝒜.piece j) ⟶ _) ≫
    (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c j).hom
  exact (hc i j W _ _).trans (congrArg₂ (fun s t => (𝒜'.mul i j).app W s t)
    (congrArg (fun k => k.hom.app W z) (Limits.prod.lift_fst a b)).symm
    (congrArg (fun k => k.hom.app W z) (Limits.prod.lift_snd a b)).symm)

variable (c) in
/-- The degreewise family out of the pullback: the identification of Stacks 03LW of the pullback
of a piece with its étale restriction, followed by the given comparison with `𝒜'`. -/
noncomputable abbrev etaleGradedPullbackPieceHom (n : ℤ) :
    (modulePullback B S hS f).obj (𝒜.piece n) ⟶ 𝒜'.piece n :=
  (modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app (𝒜.piece n) ≫ (c n).hom

/-- The underlying morphism of sheaves of sets of the degreewise family out of the pullback is
the comparison of Stacks 03LQ followed by the given comparison: this is
`AlgebraicGeometry.Space.pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback`. -/
theorem pullbackSetMap_etaleGradedPullbackPieceHom (n : ℤ) :
    pullbackSetMap (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) 𝒜 𝒜'
        (etaleGradedPullbackPieceHom c) n =
      (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
          (moduleSetSheaf B S hS Y (𝒜.piece n)) ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c n).hom := by
  refine (congrArg (fun k => pullbackScalarUnit (smallEtaleRingedToposHom B S hS f) (𝒜.piece n) ≫ k)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp
      ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app (𝒜.piece n))
      (c n).hom)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg
    (fun k => k ≫ (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c n).hom)
    (pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback B S hS f hf (𝒜.piece n))

/-- **The multiplicativity criterion holds for the degreewise family out of the pullback.**  Its
underlying morphisms of sheaves of sets are the comparison of Stacks 03LQ followed by the given
comparison, the former is natural, and the latter is multiplicative by
`AlgebraicGeometry.Space.restriction_mulSheafHom_comp`. -/
theorem isInverseImageMultiplicative_etale
    (hc : IsEtaleRestrictionMultiplicative B S hS f hf 𝒜 𝒜' c) :
    IsInverseImageMultiplicative (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) 𝒜 𝒜'
      (etaleGradedPullbackPieceHom c) := by
  intro i j
  rw [pullbackSetMap_etaleGradedPullbackPieceHom, pullbackSetMap_etaleGradedPullbackPieceHom,
    pullbackSetMap_etaleGradedPullbackPieceHom]
  exact natTrans_comp_mul_transfer (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom
    (P := moduleSetSheaf B S hS Y (𝒜.piece i)) (Q := moduleSetSheaf B S hS Y (𝒜.piece j))
    (R := moduleSetSheaf B S hS Y (𝒜.piece (i + j)))
    (P' := moduleSetSheaf B S hS X (𝒜'.piece i)) (Q' := moduleSetSheaf B S hS X (𝒜'.piece j))
    (R' := moduleSetSheaf B S hS X (𝒜'.piece (i + j)))
    (mulSheafHom 𝒜 i j) (mulSheafHom 𝒜' i j)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c i).hom)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c j).hom)
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map (c (i + j)).hom)
    (restriction_mulSheafHom_comp hc i j)

/-- **Pullback of sheaves of graded algebras along an étale morphism is restriction.**  For an
étale `f : X ⟶ Y`, a sheaf of graded `𝒪_Y`-algebras `𝒜`, and a sheaf of graded `𝒪_X`-algebras
`𝒜'` with multiplicative identifications `c_n : 𝒜_n|_{X_étale} ≅ 𝒜'_n`, the degreewise
isomorphisms `f^*𝒜_n ≅ 𝒜_n|_{X_étale} ≅ 𝒜'_n` of Stacks 03LW followed by `c_n` form an
isomorphism of sheaves of graded `𝒪_X`-algebras `f^*𝒜 ≅ 𝒜'`. -/
noncomputable def etaleGradedPullbackIso
    (hc : IsEtaleRestrictionMultiplicative B S hS f hf 𝒜 𝒜' c) :
    (gradedPull (X := smallEtaleRingedTopos B S hS X) (Y := smallEtaleRingedTopos B S hS Y)
        (smallEtaleRingedToposHom B S hS f)).obj 𝒜 ≅ 𝒜' :=
  SheafOfModules.GradedAlgebra.isoOfPieceIso
    (fun n => (modulePullbackIsoEtaleModulePullback B S hS f hf).app (𝒜.piece n) ≪≫ c n)
    (homOfInverseImageMultiplicative (X := smallEtaleRingedTopos B S hS X)
      (Y := smallEtaleRingedTopos B S hS Y) (smallEtaleRingedToposHom B S hS f) 𝒜 𝒜'
      (etaleGradedPullbackPieceHom c)
      (isInverseImageMultiplicative_etale hc)).map_mul

/-- The degree-`n` component of `AlgebraicGeometry.Space.etaleGradedPullbackIso` is the
identification of Stacks 03LW followed by the given comparison. -/
theorem etaleGradedPullbackIso_hom_app
    (hc : IsEtaleRestrictionMultiplicative B S hS f hf 𝒜 𝒜' c) (n : ℤ) :
    (etaleGradedPullbackIso hc).hom.app n =
      (modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app (𝒜.piece n) ≫ (c n).hom :=
  rfl

end AlgebraicGeometry.Space

end
