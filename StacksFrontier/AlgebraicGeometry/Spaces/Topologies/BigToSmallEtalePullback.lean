module

public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleSquare

/-!
# Sections of a pullback from the small étale topos (Stacks 0DG7)

Let `T` be a big étale site of algebraic spaces over a scheme `S`, let `X` be one of its
objects and let `F` be a sheaf on the spaces-étale site of `X`. The sections of the inverse
image `π_X⁻¹F` over an object `f : Y ⟶ X` of the big étale site of `X` are the global sections
of the small-site pullback `f_small⁻¹F` on the spaces-étale site of `Y`.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_inverseImageFactorizationIso`: the
  transitivity isomorphism `π_X⁻¹ ⋙ i_f⁻¹ ≅ f_small⁻¹`, the adjunction mate of the
  direct-image factorization of Tag 0DF6.
* `AlgebraicGeometry.BigEtaleSpaceSite.smallToBig_inverseImageSectionsIso`: global sections
  after restriction along `i_f` are evaluation at the object `f : Y ⟶ X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_inverseImageSectionsIso`: the section rule
  for `π_X⁻¹`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_inverseImageFactorizationIso_hom_app` and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigToSmall_inverseImageSectionsIso_hom_app`: the
  components of the two isomorphisms in terms of the adjunction unit and the factorization of
  Tag 0DF6.

## References

* [Stacks Project, Tag 0DG7](https://stacks.math.columbia.edu/tag/0DG7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S) {X Y : T.Spaces} (f : Y ⟶ X)

/-! ### Transitivity of inverse image -/

/-- Transitivity of inverse image for `f_small = π_X ∘ i_f`: the adjunction mate of the
direct-image factorization of Tag 0DF6, part (4). -/
@[stacks 0DG7 "transitivity of inverse image"]
noncomputable def bigToSmall_inverseImageFactorizationIso :
    (bigToSmallEtaleMorphism T X).inverseImage ⋙ (smallToBigEtaleMorphism T f).inverseImage ≅
      (smallEtaleMorphism T f).inverseImage :=
  Adjunction.leftAdjointUniq
    (((bigToSmallEtaleMorphism T X).comp (smallToBigEtaleMorphism T f)).adj.ofNatIsoRight
      (smallEtale_pushforwardIsoDirectFactorization T f).symm)
    (smallEtaleMorphism T f).adj

/-- The transitivity isomorphism is determined by the adjunction unit of `f_small` and the
direct-image factorization of Tag 0DF6: it is the morphism whose adjoint transpose is the unit
followed by that factorization. -/
@[stacks 0DG7 "the components of the transitivity isomorphism"]
theorem bigToSmall_inverseImageFactorizationIso_hom_app
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :
    (bigToSmall_inverseImageFactorizationIso T f).hom.app F =
      (((bigToSmallEtaleMorphism T X).comp
        (smallToBigEtaleMorphism T f)).adj.homEquiv _ _).symm
        ((smallEtaleMorphism T f).adj.unit.app F ≫
          (smallEtale_pushforwardIsoDirectFactorization T f).hom.app
            ((smallEtaleMorphism T f).inverseImage.obj F)) := by
  set a := ((bigToSmallEtaleMorphism T X).comp (smallToBigEtaleMorphism T f)).adj
  set e := smallEtale_pushforwardIsoDirectFactorization T f
  set b := (smallEtaleMorphism T f).adj
  rw [← Iso.symm_inv e, ← Adjunction.homEquiv_ofNatIsoRight_symm_apply a e.symm]
  exact (Equiv.eq_symm_apply _).mpr
    (Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight e.symm) b F)

/-! ### Sections after restriction along `i_f` -/

/-- Taking global sections on the spaces-étale site of `Y` after restriction along `i_f` is
evaluation at the object `f : Y ⟶ X` of the big étale site of `X`. -/
@[stacks 0DG7 "global sections after restriction are evaluation at f"]
noncomputable def smallToBig_inverseImageSectionsIso :
    (smallToBigEtaleMorphism T f).inverseImage ⋙
        Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1)) ≅
      (sheafSections (T.bigEtaleTopology X) (Type (u + 1))).obj (op (Over.mk f)) := by
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
  let R := (smallToBigEtaleMorphism T f).inverseImage
  let U := Space.SpacesEtale.final T.fppfSite S T.fppf_mem Y
  have hU : IsTerminal U := Space.SpacesEtale.final_isTerminal T.fppfSite S T.fppf_mem Y
  have hobj : (inclusionFunctor T f).obj U = Over.mk f := by
    change Over.mk (𝟙 Y ≫ f) = Over.mk f
    simp
  let γ := Sheaf.ΓNatIsoSheafSections J (Type (u + 1)) hU
  let eG (G : Sheaf (T.bigEtaleTopology X) (Type (u + 1))) :
      G.obj.obj (op (Over.mk f)) ≅ (R.obj G).obj.obj (op U) :=
    (eqToIso (congrArg (fun Z : Over X => G.obj.obj (op Z)) hobj)).symm
  have eG_hom (G : Sheaf (T.bigEtaleTopology X) (Type (u + 1))) :
      (eG G).hom = G.obj.map (eqToHom hobj).op := by
    dsimp [eG]
    rw [eqToHom_op, eqToHom_map]
  refine (NatIso.ofComponents (fun G => eG G ≪≫ (γ.app (R.obj G)).symm) ?_).symm
  intro G G' φ
  have hEval : φ.hom.app (op (Over.mk f)) ≫ (eG G').hom =
      (eG G).hom ≫ (R.map φ).hom.app (op U) := by
    have hR : (R.map φ).hom.app (op U) =
        φ.hom.app (op ((inclusionFunctor T f).obj U)) := rfl
    rw [eG_hom G', eG_hom G, hR]
    exact (φ.hom.naturality (eqToHom hobj).op).symm
  change φ.hom.app (op (Over.mk f)) ≫ ((eG G').hom ≫ γ.symm.hom.app (R.obj G')) =
    ((eG G).hom ≫ γ.symm.hom.app (R.obj G)) ≫
      (Sheaf.Γ J (Type (u + 1))).map (R.map φ)
  calc
    _ = (eG G).hom ≫ ((R.map φ).hom.app (op U) ≫ γ.symm.hom.app (R.obj G')) := by
          rw [← Category.assoc, hEval, ← Category.assoc]
    _ = (eG G).hom ≫ (γ.symm.hom.app (R.obj G) ≫
          (Sheaf.Γ J (Type (u + 1))).map (R.map φ)) := by
          rw [← Category.assoc]
          change (eG G).hom ≫
            ((sheafSections J (Type (u + 1))).obj (op U)).map (R.map φ) ≫
              γ.symm.hom.app (R.obj G') = _
          exact congrArg ((eG G).hom ≫ ·) (γ.symm.hom.naturality (R.map φ))
    _ = _ := by rw [Category.assoc]

/-! ### The section rule for the pullback -/

/-- The sections of the inverse image `π_X⁻¹F` of a sheaf on the spaces-étale site of `X` over the
object `f : Y ⟶ X` of the big étale site of `X` are the global sections of the small-site pullback
`f_small⁻¹F` on the spaces-étale site of `Y`, naturally in `F`. -/
@[stacks 0DG7 "the section rule for the pullback"]
noncomputable def bigToSmall_inverseImageSectionsIso :
    (bigToSmallEtaleMorphism T X).inverseImage ⋙
        (sheafSections (T.bigEtaleTopology X) (Type (u + 1))).obj (op (Over.mk f)) ≅
      (smallEtaleMorphism T f).inverseImage ⋙
        Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1)) :=
  Functor.isoWhiskerLeft (bigToSmallEtaleMorphism T X).inverseImage
      (smallToBig_inverseImageSectionsIso T f).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (bigToSmall_inverseImageFactorizationIso T f)
      (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) (Type (u + 1)))

/-- The section rule is the global-sections image of the transitivity isomorphism, after
identifying evaluation at `f` with global sections of the restriction along `i_f`. -/
@[stacks 0DG7 "the components of the section rule"]
theorem bigToSmall_inverseImageSectionsIso_hom_app
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :
    (bigToSmall_inverseImageSectionsIso T f).hom.app F =
      (smallToBig_inverseImageSectionsIso T f).inv.app
          ((bigToSmallEtaleMorphism T X).inverseImage.obj F) ≫
        (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
          (Type (u + 1))).map ((bigToSmall_inverseImageFactorizationIso T f).hom.app F) := by
  simp [bigToSmall_inverseImageSectionsIso]

end AlgebraicGeometry.BigEtaleSpaceSite

end
