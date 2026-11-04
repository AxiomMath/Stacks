module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTriangles
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroFunctor
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphismSymm
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Restriction and colimits of `Hom`-sets

Let `F : ℕᵒᵖ ⥤ 𝒟` be an inverse sequence and `R : 𝒟 ⥤ 𝒞` a functor such that `F ⋙ R` is the
constant system at `A`. This file complements `CategoryTheory.RestrictionLifting`, the elementwise
form of the identification `colim_n Hom_𝒟(F_n, N) = colim_n Hom_𝒞(R F_n, R N)` used for Stacks 0G2H
and Stacks 0G4Q.

## Main results

* `CategoryTheory.isColimitRestrictionHomCocone`: the elementwise identification gives the
  colimit cocone `colim_n Mor(F_n, N) = Mor(A, R N)`; this is the converse of
  `CategoryTheory.restrictionLifting_of_isColimit`.
* `CategoryTheory.RestrictionLifting.of_comp_fullyFaithful`: the identification descends along a
  fully faithful functor.
* `CategoryTheory.restrictHomIso`: if the identification holds at every object, the functor of
  points of the pro-object of `F` is `N ↦ Mor(A, R N)`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 0G4Q](https://stacks.math.columbia.edu/tag/0G4Q)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u'

namespace CategoryTheory

section Lifting

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- The converse of `CategoryTheory.restrictionLifting_of_isColimit`: if `R` identifies the two
colimits of `Hom`-sets elementwise, then the cocone of `CategoryTheory.restrictionHomCocone` is a
colimit cocone, i.e. `colim_n Mor(F_n, N) = Mor(A, R N)`. -/
public def isColimitRestrictionHomCocone (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (N : 𝒟) (A : 𝒞)
    (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A) (hF : RestrictionLifting F R N) :
    IsColimit (restrictionHomCocone F R N A e) := by
  have he : ∀ {n m : ℕ} (h : n ≤ m),
      e.inv.app (op m) ≫ R.map (InverseSequence.tr F h) = e.inv.app (op n) := fun h => by
    simpa [InverseSequence.tr] using (e.inv.naturality (homOfLE h).op).symm
  refine Types.FilteredColimit.isColimitOf _ _ (fun x => ?_) (fun i k f g hfg => ?_)
  · change A ⟶ R.obj N at x
    obtain ⟨m, hm, f, hf⟩ := hF.lift 0 (e.hom.app (op 0) ≫ x)
    refine ⟨m, f, ?_⟩
    change x = e.inv.app (op m) ≫ R.map f
    rw [hf, ← Category.assoc, he, Iso.inv_hom_id_app_assoc]
  · change F.obj (op i) ⟶ N at f
    change F.obj (op k) ⟶ N at g
    change e.inv.app (op i) ≫ R.map f = e.inv.app (op k) ≫ R.map g at hfg
    have hi : i ≤ max i k := le_max_left _ _
    have hk : k ≤ max i k := le_max_right _ _
    have hR : R.map (InverseSequence.tr F hi ≫ f) = R.map (InverseSequence.tr F hk ≫ g) := by
      apply (cancel_epi (e.inv.app (op (max i k)))).mp
      rwa [R.map_comp, R.map_comp, ← Category.assoc, ← Category.assoc, he, he]
    obtain ⟨m, hm, hmeq⟩ := hF.eq _ _ _ hR
    refine ⟨m, homOfLE (hi.trans hm), homOfLE (hk.trans hm), ?_⟩
    change F.map (homOfLE (hi.trans hm)).op ≫ f = F.map (homOfLE (hk.trans hm)).op ≫ g
    have h₁ : F.map (homOfLE (hi.trans hm)).op =
        InverseSequence.tr F hm ≫ InverseSequence.tr F hi := (tr_comp F hm hi).symm
    have h₂ : F.map (homOfLE (hk.trans hm)).op =
        InverseSequence.tr F hm ≫ InverseSequence.tr F hk := (tr_comp F hm hk).symm
    rw [h₁, h₂, Category.assoc, Category.assoc]
    exact hmeq

/-- `CategoryTheory.RestrictionLifting` descends along a fully faithful functor: the statement for
`R ⋙ E` gives it for `R`. -/
public lemma RestrictionLifting.of_comp_fullyFaithful {𝒞' : Type u'} [Category.{v} 𝒞']
    {F : ℕᵒᵖ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} {N : 𝒟} (E : 𝒞 ⥤ 𝒞') [E.Full] [E.Faithful]
    (h : RestrictionLifting F (R ⋙ E) N) : RestrictionLifting F R N where
  lift n g := by
    obtain ⟨m, hm, f, hf⟩ := h.lift n (E.map g)
    refine ⟨m, hm, f, E.map_injective ?_⟩
    change E.map (R.map f) = E.map (R.map (InverseSequence.tr F hm)) ≫ E.map g at hf
    rw [hf, E.map_comp]
  eq n f g hfg := h.eq n f g (by change E.map (R.map f) = E.map (R.map g); rw [hfg])

end Lifting

section Triangles

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

end Triangles

section Comparison

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- **The functor of points of an inverse sequence with constant restriction.** If `F ⋙ R` is
the constant system at `A` and `R` identifies the colimits of `Hom`-sets at every object, then
`colim_n Mor(F_n, -) = Mor(A, R -)`. -/
public def restrictHomIso (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (A : 𝒞)
    (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A) (hF : ∀ N, RestrictionLifting F R N) :
    Pro.seqHomColim F ≅ R ⋙ coyoneda.obj (op A) :=
  proHomComparisonIso F R (coneOfNatIso e ⟨A, 𝟙 _⟩) (op 0) (e.hom.app (op 0) ≫ 𝟙 A)
    (essentiallyConstantWith_of_natIso e ⟨A, 𝟙 _⟩ (op 0) (𝟙 A)
      (essentiallyConstantWith_const A)) hF

end Comparison

section Deligne

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

namespace DeligneSystemValues

variable {jstar : 𝒟 ⥤ 𝒞} (A : DeligneSystemValues jstar)

end DeligneSystemValues

end Deligne

section Main

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

end Main

end CategoryTheory

end
