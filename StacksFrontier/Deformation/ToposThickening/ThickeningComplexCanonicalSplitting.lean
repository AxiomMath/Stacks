module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposCoefficientChangeModules
public import StacksFrontier.CategoryTheory.Sites.CommRingSheafFactorization
public import StacksFrontier.Deformation.ToposThickening.ThickeningComplexBoundary

/-!
# The canonical splitting of the first thickening of a complex of thickenings

Let `O'₃ ⟶ O'₂ ⟶ O'₁` be a complex of first order thickenings of a ringed topos `(Sh(C), O)`,
presented on one site. Remark **Stacks 08ML** observes that the composite
`(Sh(D₁), O'₁) ⟶ (Sh(D₃), O'₃)` factors through `(Sh(C), O)`, so that the first thickening is
trivial and comes with a canonical trivialization `π`. On structure sheaves this is the
statement that the composite `O'₃ ⟶ O'₂ ⟶ O'₁` kills the defining ideal `I₃` of the third
thickening, and therefore factors through its quotient `O'₃ ⟶ O`.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickeningComplex.canonicalSplittingRingHom`: the map
  `O ⟶ O'₁` of sheaves of rings through which `O'₃ ⟶ O'₁` factors.

## Main results

* `Deformation.ToposThickening.FirstOrderThickeningComplex.fSharp₃_comp_canonicalSplittingRingHom`:
  it factors the composite `O'₃ ⟶ O'₂ ⟶ O'₁`.
* `Deformation.ToposThickening.FirstOrderThickeningComplex.canonicalSplittingRingHom_comp`:
  it is a section of the structure map `O'₁ ⟶ O`.

## References

* [Stacks Project, Tag 08ML](https://stacks.math.columbia.edu/tag/08ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u'

namespace Deformation.ToposThickening

namespace FirstOrderThickeningComplex

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {i : RingedToposHom X Y} (S : FirstOrderThickeningComplex i)

/-- **The composite `O'₃ ⟶ O'₂ ⟶ O'₁` of a complex kills the defining ideal of `O'₃`.** A local
section killed by the structure map `O'₃ ⟶ O` is a section `b` of `I₃`, and its image in `O'₁` is
the image of `b` under the composite map of defining ideals, which vanishes. -/
theorem h₃₂_comp_hSharp_apply_eq_zero (hS : S.IsComplex) (U : Y.Cᵒᵖ) (x : S.O₃.obj.obj U)
    (hx : S.fSharp₃.hom.app U x = 0) : (S.h₃₂ ≫ S.lower.hSharp).hom.app U x = 0 := by
  obtain ⟨b, hb⟩ := (S.third.kernel U x).1 hx
  have h := S.whole.inclOne_idealMap U b
  rw [(S.isComplex_iff_whole_idealMap_eq_zero).1 hS] at h
  have h0 : S.whole.inclOne U ((0 : S.whole.second.I ⟶ S.whole.first.I).val.app U b) = 0 :=
    map_zero (S.whole.first.incl.val.app U).hom
  rw [h0] at h
  rw [← hb]
  exact h.symm

/-- **The canonical splitting of Remark Stacks 08ML, on structure sheaves.** The composite
`O'₃ ⟶ O'₂ ⟶ O'₁` of a complex of first order thickenings kills the defining ideal of `O'₃`, so it
descends along the locally surjective structure map `O'₃ ⟶ O` to a map `O ⟶ O'₁`. -/
noncomputable def canonicalSplittingRingHom (hS : S.IsComplex) : baseRing i ⟶ Y.O :=
  ObjectProperty.homMk (Stacks.Sites.existsUnique_commRingFactor S.fSharp₃.hom
    (S.h₃₂ ≫ S.lower.hSharp).hom S.third.surjective
    (Stacks.Sites.isSheaf_comp_forget_commRingCat Y.O.property)
    (S.h₃₂_comp_hSharp_apply_eq_zero hS)).exists.choose

/-- The canonical splitting factors the composite `O'₃ ⟶ O'₂ ⟶ O'₁` through `O'₃ ⟶ O`. -/
theorem fSharp₃_comp_canonicalSplittingRingHom (hS : S.IsComplex) :
    S.fSharp₃ ≫ S.canonicalSplittingRingHom hS = S.h₃₂ ≫ S.lower.hSharp :=
  Sheaf.hom_ext (Stacks.Sites.existsUnique_commRingFactor _ _ S.third.surjective
    (Stacks.Sites.isSheaf_comp_forget_commRingCat Y.O.property)
    (S.h₃₂_comp_hSharp_apply_eq_zero hS)).exists.choose_spec

/-- The canonical splitting is a section of the structure map `O'₁ ⟶ O` of the first
thickening. -/
theorem canonicalSplittingRingHom_comp (hS : S.IsComplex) :
    S.canonicalSplittingRingHom hS ≫ i.fSharp = 𝟙 (baseRing i) := by
  refine Sheaf.hom_ext (Stacks.Sites.commRingHom_ext_of_isLocallySurjective S.fSharp₃.hom
    S.third.surjective (Stacks.Sites.isSheaf_comp_forget_commRingCat (baseRing i).property) ?_)
  have h : S.fSharp₃ ≫ S.canonicalSplittingRingHom hS ≫ i.fSharp =
      S.fSharp₃ ≫ 𝟙 (baseRing i) := by
    rw [← Category.assoc, S.fSharp₃_comp_canonicalSplittingRingHom hS, Category.assoc,
      S.lower.comm, S.comm₃, Category.comp_id]
  exact congrArg (fun k ↦ k.hom) h

/-- The base ringed topos `(Sh(C), O)` presented on the site of the thickening: the ringed topos
`(Sh(D), i_*O)`, together with the equivalence `ι : (Sh(C), O) ⟶ (Sh(D), i_*O)` whose structure map
is the identity. -/
noncomputable abbrev baseEquivalence (i : RingedToposHom X Y) :
    RingedToposHom X (reshape Y (baseRing i)) :=
  reshapeHom i (baseRing i) (𝟙 _)

/-- **The canonical splitting `π : (Sh(D₁), O'₁) ⟶ (Sh(C), O)` of Remark Stacks 08ML**: the change
of coefficients along the canonical splitting `O ⟶ O'₁` of structure sheaves, followed by the
inverse of the equivalence `ι : (Sh(C), O) ⟶ (Sh(D), i_*O)`. -/
noncomputable def canonicalRetraction (hS : S.IsComplex) : RingedToposHom Y X :=
  haveI : i.toToposHom.pushforward.IsEquivalence := S.lower.first.equiv
  (RingedToposHom.inverse (baseEquivalence i)).comp
    (RingedToposHom.coefficientMorphism Y.J (S.canonicalSplittingRingHom hS))

/-- The counit `i⁻¹i_* ⟶ 𝟭` of the adjunction `i⁻¹ ⊣ i_*` of a first order thickening, an
isomorphism because `i_*` is an equivalence of topoi. -/
noncomputable def counitIso : i.toToposHom.pushforward ⋙ i.toToposHom.inverseImage ≅ 𝟭 X.Topos :=
  haveI : i.toToposHom.pushforward.IsEquivalence := S.lower.first.equiv
  asIso i.toToposHom.adj.counit

/-- The forward map of `S.counitIso` is the counit of the adjunction `i⁻¹ ⊣ i_*`. -/
@[simp]
theorem counitIso_hom : S.counitIso.hom = i.toToposHom.adj.counit := rfl

/-- The structure map `i_*O ⟶ O'₁` read back on `(Sh(C), O)` through `ι` is the counit of
`i⁻¹ ⊣ i_*`, on underlying sheaves of sets. -/
theorem forgetRing_map_baseEquivalence_fSharpInverseImage :
    X.forgetRing.map (baseEquivalence i).fSharpInverseImage =
      S.counitIso.hom.app (X.forgetRing.obj X.O) := by
  have h : (baseEquivalence i).fSharp = 𝟙 (baseRing i) := rfl
  rw [RingedToposHom.fSharpInverseImage_forget, h, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id]
  exact Category.id_comp _

/-- On underlying sheaves of sets, the structure map of the canonical retraction is the inverse
of the counit of `i⁻¹ ⊣ i_*` followed by the inverse image of the canonical splitting. -/
theorem forgetRing_map_canonicalRetraction_fSharp (hS : S.IsComplex) :
    X.forgetRing.map (S.canonicalRetraction hS).fSharp =
      S.counitIso.inv.app (X.forgetRing.obj X.O) ≫
        i.toToposHom.inverseImage.map
          ((sheafCompose Y.J (forget CommRingCat.{w})).map (S.canonicalSplittingRingHom hS)) := by
  have : i.toToposHom.pushforward.IsEquivalence := S.lower.first.equiv
  have h₂ := RingedToposHom.comp_fSharp_forget (RingedToposHom.inverse (baseEquivalence i))
    (RingedToposHom.coefficientMorphism Y.J (S.canonicalSplittingRingHom hS))
  have h₃ : X.forgetRing.map (RingedToposHom.inverse (baseEquivalence i)).fSharp =
      S.counitIso.inv.app (X.forgetRing.obj X.O) := by
    rw [RingedToposHom.inverse_fSharp, CategoryTheory.Functor.map_inv]
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [S.forgetRing_map_baseEquivalence_fSharpInverseImage]
    exact S.counitIso.hom_inv_id_app _
  unfold canonicalRetraction
  rw [h₂, h₃,
    RingedToposHom.forgetRing_map_coefficientMorphism_fSharp Y.J (S.canonicalSplittingRingHom hS)]
  rfl

/-- On underlying sheaves of sets, the structure map of the round trip
`(Sh(C), O) ⟶ (Sh(D₁), O'₁) ⟶ (Sh(C), O)` through the canonical splitting is the inverse of the
counit of `i⁻¹ ⊣ i_*`. -/
theorem forgetRing_map_canonicalRetraction_comp_fSharp (hS : S.IsComplex) :
    X.forgetRing.map ((S.canonicalRetraction hS).comp i).fSharp =
      S.counitIso.inv.app (X.forgetRing.obj X.O) := by
  rw [RingedToposHom.comp_fSharp_forget, S.forgetRing_map_canonicalRetraction_fSharp hS]
  have h₄ : (sheafCompose Y.J (forget CommRingCat.{w})).map (S.canonicalSplittingRingHom hS) ≫
      Y.forgetRing.map i.fSharp = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, S.canonicalSplittingRingHom_comp hS,
      CategoryTheory.Functor.map_id]
  refine (Category.assoc _ _ _).trans ((congrArg
    (fun m ↦ S.counitIso.inv.app (X.forgetRing.obj X.O) ≫ m)
    ((i.toToposHom.inverseImage.map_comp
      ((sheafCompose Y.J (forget CommRingCat.{w})).map (S.canonicalSplittingRingHom hS))
      (Y.forgetRing.map i.fSharp)).symm.trans ?_)).trans (Category.comp_id _))
  rw [h₄]
  exact i.toToposHom.inverseImage.map_id _

/-- **The canonical trivialization `π` of the first thickening of a complex**, Remark
Stacks 08ML: the retraction `S.canonicalRetraction hS` of `i`. The round trip through it is the
identity up to the counit of `i⁻¹ ⊣ i_*`, which is an isomorphism because `i` identifies the
underlying topoi. -/
noncomputable def canonicalTrivialization (hS : S.IsComplex) : Trivialization i where
  retraction := S.canonicalRetraction hS
  comp_id := ⟨S.counitIso, by
    rw [S.forgetRing_map_canonicalRetraction_comp_fSharp hS]
    exact S.counitIso.inv_hom_id_app _⟩

/-- After pushing forward along the canonical retraction, the splitting of the structure map
supplied by the canonical trivialization agrees with the canonical splitting `O ⟶ O'₁`. -/
theorem pushforward_map_splitting_canonicalTrivialization (hS : S.IsComplex) :
    (pushforwardCommRingFunctor (S.canonicalTrivialization hS).retraction.toToposHom).map
        (Sheaf.homEquiv.symm
          (splittingFromTrivialization i S.lower.first (S.canonicalTrivialization hS)).1) =
      (pushforwardCommRingFunctor (S.canonicalTrivialization hS).retraction.toToposHom).map
        (S.canonicalSplittingRingHom hS) := by
  have hcomp : X.forgetRing.map ((S.canonicalTrivialization hS).retraction.comp i).fSharp =
      S.counitIso.inv.app (X.forgetRing.obj X.O) :=
    S.forgetRing_map_canonicalRetraction_comp_fSharp hS
  have hret : X.forgetRing.map (S.canonicalTrivialization hS).retraction.fSharp =
      S.counitIso.inv.app (X.forgetRing.obj X.O) ≫
        i.toToposHom.inverseImage.map
          ((sheafCompose Y.J (forget CommRingCat.{w})).map (S.canonicalSplittingRingHom hS)) :=
    S.forgetRing_map_canonicalRetraction_fSharp hS
  have hφ : IsIso ((S.canonicalTrivialization hS).retraction.comp i).fSharp := by
    have : IsIso (X.forgetRing.map ((S.canonicalTrivialization hS).retraction.comp i).fSharp) := by
      rw [hcomp]
      exact (S.counitIso.app _).isIso_inv
    exact isIso_of_reflects_iso _ X.forgetRing
  have hinv : X.forgetRing.map (inv ((S.canonicalTrivialization hS).retraction.comp i).fSharp) =
      S.counitIso.hom.app (X.forgetRing.obj X.O) := by
    rw [CategoryTheory.Functor.map_inv]
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [hcomp]
    exact S.counitIso.inv_hom_id_app _
  unfold splittingFromTrivialization
  dsimp only
  have hcancel : ∀ {A B : Sheaf Y.J CommRingCat.{w}} (f : A ⟶ B),
      Sheaf.homEquiv.symm f.hom = f := fun _ ↦ rfl
  rw [hcancel, Functor.FullyFaithful.map_preimage]
  apply X.forgetRing.map_injective
  refine (X.forgetRing.map_comp _ _).trans ?_
  refine (congrArg (· ≫ X.forgetRing.map (S.canonicalTrivialization hS).retraction.fSharp)
    ((X.forgetRing.map_comp
      (Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso i.toToposHom
        (S.canonicalTrivialization hS).retraction.toToposHom X.O).hom
      (@CategoryTheory.inv _ _ _ _ ((S.canonicalTrivialization hS).retraction.comp i).fSharp
        hφ)).trans
      ((congrArg (· ≫ _)
        (Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso_hom_forget _ _ _)).trans
        ((Category.id_comp _).trans hinv)))).trans ?_
  rw [hret]
  exact (S.counitIso.hom_inv_id_app_assoc _ _).trans
    (Stacks.Sheaves.ToposPullback.underlyingRingSheaf_map_pullbackCommRingSheafMap X.J _ _).symm

/-- **The splitting of the structure map supplied by the canonical trivialization is the canonical
splitting of structure sheaves.** -/
theorem splittingRingHom_canonicalTrivialization (hS : S.IsComplex) :
    splittingRingHom i S.lower.first (S.canonicalTrivialization hS) =
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map (S.canonicalSplittingRingHom hS) := by
  have : i.toToposHom.pushforward.IsEquivalence := S.lower.first.equiv
  have hj : (S.canonicalTrivialization hS).retraction.toToposHom.pushforward.IsEquivalence := by
    change (𝟭 _ ⋙ i.toToposHom.inverseImage).IsEquivalence
    infer_instance
  have := Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor_isEquivalence _ hj
  unfold splittingRingHom
  congr 1
  exact (pushforwardCommRingFunctor
    (S.canonicalTrivialization hS).retraction.toToposHom).map_injective
    (S.pushforward_map_splitting_canonicalTrivialization hS)

/-- **The canonical trivialization is the canonical splitting of Remark Stacks 08ML**: the
composite `O'₃ ⟶ O'₂ ⟶ O'₁` of the complex factors through `O'₃ ⟶ O` followed by the splitting
`O ⟶ O'₁` the trivialization supplies. This is the condition under which the boundary
computation of Remark Stacks 08MM is stated. -/
theorem upper_ringMapH_comp_lower_ringMapH_eq (hS : S.IsComplex) :
    S.upper.ringMapH ≫ S.lower.ringMapH =
      S.whole.ringMap₂ ≫ splittingRingHom i S.lower.first (S.canonicalTrivialization hS) := by
  rw [S.splittingRingHom_canonicalTrivialization hS]
  change (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.h₃₂ ≫
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.lower.hSharp =
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map S.fSharp₃ ≫ _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    S.fSharp₃_comp_canonicalSplittingRingHom hS]

end FirstOrderThickeningComplex

end Deformation.ToposThickening

end
