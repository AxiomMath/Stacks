module

public import StacksFrontier.Deformation.ToposThickening.FirstOrderThickeningOfProperty
public import StacksFrontier.Deformation.ToposThickening.BaseThickeningInverseImage
public import StacksFrontier.Deformation.ToposThickening.FlatLiftFlatnessCriterion
public import StacksFrontier.Deformation.ToposThickening.TrivializedThickeningComparison
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback

/-!
# The square of Situation 08M7 with its base read on the thickened topos

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` and `t : (Sh(ℬ), O_ℬ) ⟶ (Sh(ℬ'), O_{ℬ'})` be first order
thickenings of ringed topoi and let `f' : (Sh(D), O') ⟶ (Sh(ℬ'), O_{ℬ'})` and
`p : (Sh(C), O) ⟶ (Sh(ℬ), O_ℬ)` be morphisms of ringed topoi such that `f' ∘ i` and `t ∘ p`
agree on structure sheaves up to an isomorphism `θ : f'_*i_*O ≅ t_*p_*O` of their direct images.
The square of Stacks 08M7 asks the square to commute on the nose, which for morphisms of ringed
topoi built from geometry (for instance the morphisms of small étale ringed topoi of Stacks 03G8,
which are only pseudo-functorial) is not available.

The source's proofs only ever use the base through the sheaves of rings `f⁻¹O_{ℬ'}` and
`f⁻¹O_ℬ` on the thickened topos (see `Deformation.ToposThickening.inverseImageBaseRing`). This file
replaces the base by those sheaves of rings: the ringed topoi `(Sh(D), f'⁻¹O_{ℬ'})` and
`(Sh(D), f'⁻¹t_*O_ℬ)`, the thickening `t̃ = (id, f'⁻¹t^♯)` between them, the morphism
`f̃' = (id, f'^♯)` and the morphism `f̃ = (i, f̃^♯)` whose structure map is transported from `p`
along `θ`. The resulting square commutes on the nose.

## Main definitions

* `Deformation.ToposThickening.relBaseTop` and `relBaseBottom`: the ringed topoi
  `(Sh(D), f'⁻¹O_{ℬ'})` and `(Sh(D), f'⁻¹t_*O_ℬ)`.
* `Deformation.ToposThickening.relBaseRight` (`f̃'`), `relBaseThickening` (`t̃`) and
  `relBaseLeft` (`f̃`).

## Main results

* `Deformation.ToposThickening.relBase_comm`: `f̃' ∘ i = t̃ ∘ f̃`.
* `Deformation.ToposThickening.relBaseThickening_isFirstOrderThickening`: `t̃` is a first order
  thickening; `relBaseThickeningFirstOrderThickening` is the datum of Stacks 08MB that goes with
  it.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor inverseImageCommRingFunctor
  commRingImageAdjunction pushforwardCommRingCompIso)
open Stacks.Sheaves.ToposPullback (pullbackCommRingSheafFunctorId)

universe v u w v' u' vS uS wS vS' uS'

namespace Deformation.ToposThickening

/-- An isomorphism of sheaves of commutative rings, applied after its inverse on sections, is
the identity (for arbitrary site and section universes). -/
theorem Sheaf.commRingIso_hom_inv_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q : Sheaf J CommRingCat.{w}} (e : P ≅ Q) (U : Cᵒᵖ) (b : Q.obj.obj U) :
    (e.hom.hom.app U).hom ((e.inv.hom.app U).hom b) = b := by
  have h : e.inv.hom.app U ≫ e.hom.hom.app U = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom, e.inv_hom_id]
    rfl
  exact ConcreteCategory.congr_hom h b

section RelativeBase

variable {X : RingedTopos.{v, u, w}} {X' : RingedTopos.{v', u', w}}
  {S : RingedTopos.{vS, uS, w}} {S' : RingedTopos.{vS', uS', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w})]
  [S.J.HasSheafCompose (forget RingCat.{w})] [S'.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [S'.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  (i : RingedToposHom X X') (t : RingedToposHom S S') (f' : RingedToposHom X' S')
  (p : RingedToposHom X S)

/-- **The thickened base, read on the thickened topos**: `(Sh(D), f'⁻¹O_{ℬ'})`. -/
noncomputable abbrev relBaseTop : RingedTopos.{v', u', w} :=
  ringedToposOn X'.J (inverseImageBaseRing f')

/-- **The base, read on the thickened topos**: `(Sh(D), f'⁻¹t_*O_ℬ)`. -/
noncomputable abbrev relBaseBottom : RingedTopos.{v', u', w} :=
  ringedToposOn X'.J (inverseImageReducedBaseRing t f')

/-- **The morphism `f̃' = (id, f'^♯) : (Sh(D), O') ⟶ (Sh(D), f'⁻¹O_{ℬ'})`**, whose structure map is
the inverse-image form `f'⁻¹O_{ℬ'} ⟶ O'` of that of `f'`. -/
noncomputable def relBaseRight : RingedToposHom X' (relBaseTop f') :=
  homOn (MorphismOfTopoi.id X'.Topos)
    (f'.fSharpInverseImage ≫ (pullbackCommRingSheafFunctorId X'.J).inv.app X'.O)

/-- **The thickening `t̃ = (id, f'⁻¹t^♯) : (Sh(D), f'⁻¹t_*O_ℬ) ⟶ (Sh(D), f'⁻¹O_{ℬ'})`.** -/
noncomputable def relBaseThickening : RingedToposHom (relBaseBottom t f') (relBaseTop f') :=
  homOn (X := relBaseBottom t f') (MorphismOfTopoi.id X'.Topos)
    (inverseImageBaseReduction t f' ≫
      (pullbackCommRingSheafFunctorId X'.J).inv.app (inverseImageReducedBaseRing t f'))

variable (θ : (pushforwardCommRingFunctor f'.toToposHom).obj
    ((pushforwardCommRingFunctor i.toToposHom).obj X.O) ≅
  (pushforwardCommRingFunctor t.toToposHom).obj
    ((pushforwardCommRingFunctor p.toToposHom).obj X.O))

/-- **The structure map `f'⁻¹t_*O_ℬ ⟶ i_*O` of `f̃`**: the adjoint transpose of
`t_*O_ℬ ⟶ t_*p_*O ≅ f'_*i_*O`, the direct image of the structure map of `p` transported along
`θ`. -/
noncomputable def relBaseLeftSharp :
    inverseImageReducedBaseRing t f' ⟶ (pushforwardCommRingFunctor i.toToposHom).obj X.O :=
  ((commRingImageAdjunction f'.toToposHom).homEquiv _ _).symm
    ((pushforwardCommRingFunctor t.toToposHom).map p.fSharp ≫ θ.inv)

/-- **The morphism `f̃ = (i, f̃^♯) : (Sh(C), O) ⟶ (Sh(D), f'⁻¹t_*O_ℬ)`**, with the underlying
morphism of topoi of `i`. -/
noncomputable def relBaseLeft : RingedToposHom X (relBaseBottom t f') :=
  homOn i.toToposHom (relBaseLeftSharp i t f' p θ)

variable {i t f' p θ}

omit [X'.J.HasSheafCompose (forget AddCommGrpCat)] [S'.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The reduction followed by the structure map of `f̃` is `f'^♯` followed by `i^♯`**, granted
the compatibility of `θ` with the structure maps of `f' ∘ i` and `t ∘ p`. -/
theorem inverseImageBaseReduction_comp_relBaseLeftSharp
    (hθ : f'.fSharp ≫ (pushforwardCommRingFunctor f'.toToposHom).map i.fSharp ≫ θ.hom =
      t.fSharp ≫ (pushforwardCommRingFunctor t.toToposHom).map p.fSharp) :
    inverseImageBaseReduction t f' ≫ relBaseLeftSharp i t f' p θ =
      f'.fSharpInverseImage ≫ i.fSharp := by
  refine ((commRingImageAdjunction f'.toToposHom).homEquiv_naturality_left_symm _ _).symm.trans
    (Eq.trans ?_ ((commRingImageAdjunction f'.toToposHom).homEquiv_naturality_right_symm _ _))
  congr 1
  rw [← Category.assoc, ← hθ]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

omit [X'.J.HasSheafCompose (forget AddCommGrpCat)] [S'.J.HasSheafCompose (forget AddCommGrpCat)] in
/-- **The square commutes on the nose: `f̃' ∘ i = t̃ ∘ f̃`.** -/
theorem relBase_comm
    (hθ : f'.fSharp ≫ (pushforwardCommRingFunctor f'.toToposHom).map i.fSharp ≫ θ.hom =
      t.fSharp ≫ (pushforwardCommRingFunctor t.toToposHom).map p.fSharp) :
    (relBaseRight f').comp i = (relBaseThickening t f').comp (relBaseLeft i t f' p θ) := by
  have h₁ := (pullbackCommRingSheafFunctorId X'.J).inv.naturality i.fSharp
  have h₂ := (pullbackCommRingSheafFunctorId X'.J).inv.naturality (relBaseLeftSharp i t f' p θ)
  have key : (f'.fSharpInverseImage ≫ (pullbackCommRingSheafFunctorId X'.J).inv.app X'.O) ≫
        (pushforwardCommRingFunctor (MorphismOfTopoi.id X'.Topos)).map i.fSharp =
      (inverseImageBaseReduction t f' ≫ (pullbackCommRingSheafFunctorId X'.J).inv.app
          (inverseImageReducedBaseRing t f')) ≫
        (pushforwardCommRingFunctor (MorphismOfTopoi.id X'.Topos)).map
          (relBaseLeftSharp i t f' p θ) :=
    (Category.assoc _ _ _).trans ((congrArg (f'.fSharpInverseImage ≫ ·) h₁.symm).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg
        (· ≫ (pullbackCommRingSheafFunctorId X'.J).inv.app
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
          (inverseImageBaseReduction_comp_relBaseLeftSharp hθ).symm).trans
        ((Category.assoc _ _ _).trans ((congrArg (inverseImageBaseReduction t f' ≫ ·) h₂).trans
          (Category.assoc _ _ _).symm)))))
  unfold RingedToposHom.comp
  exact congrArg (fun s => (⟨(MorphismOfTopoi.id X'.Topos).comp i.toToposHom, s⟩ :
    RingedToposHom X (relBaseTop f'))) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _)))

variable [HasSheafify X'.J AddCommGrpCat.{w}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify X'.J AddCommGrpCat.{w}]

/-- **The thickening `t̃ = (id, f'⁻¹t^♯)` is a first order thickening** (Stacks 08M7): its
underlying morphism of topoi is the identity, the reduction `f'⁻¹O_{ℬ'} ⟶ f'⁻¹t_*O_ℬ` is locally
surjective, and its kernel is the inverse image `f'⁻¹𝒥` of the square-zero ideal, which is killed
by the kernel because it is a module over `f'⁻¹t_*O_ℬ`. -/
theorem relBaseThickening_isFirstOrderThickening (ht : FirstOrderThickening t) :
    IsFirstOrderThickening (relBaseThickening t f') := by
  have hker : ∀ (U : X'.Cᵒᵖ) (a : (inverseImageBaseRing f').obj.obj U),
      (relBaseThickening t f').fSharp.hom.app U a = 0 →
        (inverseImageBaseReduction t f').hom.app U a = 0 := by
    intro U a ha
    have h := congrArg (((pullbackCommRingSheafFunctorId X'.J).hom.app
      (inverseImageReducedBaseRing t f')).hom.app U).hom ha
    exact (Sheaf.commRingIso_hom_inv_app_apply ((pullbackCommRingSheafFunctorId X'.J).app
      (inverseImageReducedBaseRing t f')) U _).symm.trans (h.trans (map_zero _))
  have hsq : ∀ (U : X'.Cᵒᵖ) (a b : (inverseImageBaseRing f').obj.obj U),
      (relBaseThickening t f').fSharp.hom.app U a = 0 →
        (relBaseThickening t f').fSharp.hom.app U b = 0 → a * b = 0 := by
    intro U a b ha hb
    obtain ⟨α, hα, -⟩ := existsUnique_inverseImageBaseIdeal_section t f' ht U a (hker U a ha)
    obtain ⟨β, hβ, -⟩ := existsUnique_inverseImageBaseIdeal_section t f' ht U b (hker U b hb)
    rw [← hα, ← hβ]
    exact mul_eq_zero_of_inverseImageBaseIdeal t f' ht U α β
  refine ⟨⟨?_, ?_, fun U a ha => ⟨⊤, X'.J.top_mem _, fun V p _ => ⟨2, ?_⟩⟩⟩, hsq⟩
  · exact (inferInstance : (𝟭 X'.Topos).IsEquivalence)
  · have := isLocallySurjective_inverseImageBaseReduction t f' ht
    have : IsIso ((pullbackCommRingSheafFunctorId X'.J).inv.app
        (inverseImageReducedBaseRing t f')).hom :=
      (inferInstance : IsIso ((sheafToPresheaf X'.J CommRingCat.{w}).map
        ((pullbackCommRingSheafFunctorId X'.J).inv.app (inverseImageReducedBaseRing t f'))))
    exact Presheaf.isLocallySurjective_comp X'.J (inverseImageBaseReduction t f').hom
      ((pullbackCommRingSheafFunctorId X'.J).inv.app (inverseImageReducedBaseRing t f')).hom
  · rw [pow_two, ← map_mul, hsq U a a ha ha, map_zero]

/-- **The first order thickening `t̃ = (id, f'⁻¹t^♯)`**, with its square-zero ideal (Stacks 08MB);
see `Deformation.ToposThickening.relBaseThickening_isFirstOrderThickening`. -/
noncomputable def relBaseThickeningFirstOrderThickening (ht : FirstOrderThickening t) :
    FirstOrderThickening (relBaseThickening t f') :=
  FirstOrderThickening.ofIsFirstOrderThickening (relBaseThickening_isFirstOrderThickening ht)

end RelativeBase

end Deformation.ToposThickening

end
