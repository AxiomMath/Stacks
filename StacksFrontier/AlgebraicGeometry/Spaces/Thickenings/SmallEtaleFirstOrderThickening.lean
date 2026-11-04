module

public import StacksFrontier.Deformation.ToposThickening.FirstOrderThickeningOfProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleRingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Order
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionChartBaseChangeDense
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism

/-!
# A first order thickening of algebraic spaces is one of small étale ringed topoi

Let `i : Z ⟶ Z'` be a morphism of algebraic spaces over `S` which is a first order thickening:
it identifies `Z` with a closed subspace of `Z'` whose defining ideal has square zero on every
object of the small étale site. Then the induced morphism of small étale ringed topoi
`(Z_étale, 𝒪_Z) ⟶ (Z'_étale, 𝒪_{Z'})` of Stacks 03G8 is a first order thickening of ringed topoi
in the sense of Stacks 08M7 and 08MB. This is the first-order half of the content of
Stacks 0D16, which is registered elsewhere; it is stated here unregistered, in the form the
deformation theory of the functor of quotients (Stacks 0CZU) consumes.

## Main results

* `AlgebraicGeometry.Space.isEquivalence_smallToposMorphismTypeU_pushforward_of_isThickeningHom`:
  the direct image along a thickening of algebraic spaces is an equivalence of small étale topoi
  (Stacks 05ZJ, for a thickening given by a morphism rather than a subspace).
* `AlgebraicGeometry.Space.isFirstOrderThickening_smallEtaleRingedToposHom`: the morphism of small
  étale ringed topoi of a first order thickening is a first order thickening of ringed topoi.
* `AlgebraicGeometry.Space.smallEtaleRingedToposHomFirstOrderThickening`: the datum of
  Stacks 08MB that goes with it.

## References

* [Stacks Project, Tag 0D16](https://stacks.math.columbia.edu/tag/0D16)
* [Stacks Project, Tag 05ZJ](https://stacks.math.columbia.edu/tag/05ZJ)
* [Stacks Project, Tag 05ZK](https://stacks.math.columbia.edu/tag/05ZK)
* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The factorization `Z ≅ i(Z) ⊂ Z'` of a morphism of algebraic spaces through its range. -/
theorem homMk_toRange_comp_inclusion {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z')
    (hi : IsThickeningHom B S hS i) :
    (ObjectProperty.homMk (Subfunctor.toRange i.hom) :
        Z ⟶ IsThickening.space B S hS hi.2) ≫ IsThickening.inclusion B S hS hi.2 = i := by
  ext1
  exact Subfunctor.toRange_ι i.hom

/-- The inverse of `Z ≅ i(Z)` followed by the factorization `Z ⟶ i(Z)` is the identity. -/
private theorem homMk_inv_comp_homMk_toRange {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z')
    (hi : IsThickeningHom B S hS i) :
    (ObjectProperty.homMk (@inv _ _ _ _ (Subfunctor.toRange i.hom) hi.1) :
        IsThickening.space B S hS hi.2 ⟶ Z) ≫
      (ObjectProperty.homMk (Subfunctor.toRange i.hom) : Z ⟶ IsThickening.space B S hS hi.2) =
        𝟙 _ := by
  ext1
  exact @IsIso.inv_hom_id _ _ _ _ _ hi.1

/-- **The direct image along a thickening of algebraic spaces is an equivalence of small étale
topoi** (Stacks 05ZJ), for a thickening given by a morphism `i : Z ⟶ Z'`: it is fully faithful,
`i` being a closed immersion (Stacks 04E5), and essentially surjective, because it agrees, up to
the isomorphism `Z ≅ i(Z)`, with the direct image along the inclusion of the subspace `i(Z)`. -/
theorem isEquivalence_smallToposMorphismTypeU_pushforward_of_isThickeningHom
    {Z Z' : AlgebraicSpaces B S hS} (i : Z ⟶ Z') (hi : IsThickeningHom B S hS i) :
    (smallToposMorphismTypeU B S hS i).pushforward.IsEquivalence := by
  have hff := fullyFaithfulSmallEtalePushforwardOfIsClosedImmersion B S hS i
    hi.isClosedImmersion
  have := isEquivalence_smallEtalePushforward_of_isThickening B S hS hi.2
  have : IsIso (Subfunctor.toRange i.hom) := hi.1
  have hψ : (ObjectProperty.homMk (@inv _ _ _ _ (Subfunctor.toRange i.hom) hi.1) :
      IsThickening.space B S hS hi.2 ⟶ Z) ≫ i = IsThickening.inclusion B S hS hi.2 := by
    refine (congrArg (_ ≫ ·) (homMk_toRange_comp_inclusion B S hS i hi).symm).trans ?_
    rw [← Category.assoc, homMk_inv_comp_homMk_toRange B S hS i hi, Category.id_comp]
  refine { faithful := hff.faithful, full := hff.full, essSurj := ⟨fun H => ?_⟩ }
  obtain ⟨F₀, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (smallToposMorphismTypeU B S hS
    (IsThickening.inclusion B S hS hi.2)).pushforward H
  refine ⟨(smallToposMorphismTypeU B S hS (ObjectProperty.homMk (@inv _ _ _ _ (Subfunctor.toRange
    i.hom) hi.1) : IsThickening.space B S hS hi.2 ⟶ Z)).pushforward.obj F₀, ⟨?_⟩⟩
  refine ((smallToposMorphismTypeU_comp B S hS _ i).app F₀) ≪≫ eqToIso ?_ ≪≫ e
  rw [hψ]

/-- The structure map of a morphism of algebraic spaces equal to an identity is invertible. -/
theorem isIso_fSharp_of_eq_id {A : AlgebraicSpaces B S hS} (p : A ⟶ A) (hp : p = 𝟙 A) :
    IsIso (smallEtaleRingedToposHom B S hS p).fSharp := by
  subst hp
  exact isIso_fSharp_id B S hS A

/-- **The structure map of a morphism with a left inverse is a split monomorphism**: if
`b ≫ a = 𝟙`, the structure map of `a` has a retraction, built from the structure map of `b` and
the compatibility of structure maps with composition (Stacks 03G8). -/
theorem exists_retraction_fSharp {X₁ X₂ : AlgebraicSpaces B S hS} (a : X₁ ⟶ X₂) (b : X₂ ⟶ X₁)
    (hba : b ≫ a = 𝟙 X₂) :
    ∃ r, (smallEtaleRingedToposHom B S hS a).fSharp ≫ r = 𝟙 _ := by
  have := isIso_fSharp_of_eq_id B S hS (b ≫ a) hba
  exact ⟨_, (fSharp_comp_compRingIso B S hS b a
    (inv (smallEtaleRingedToposHom B S hS (b ≫ a)).fSharp)).trans (IsIso.hom_inv_id _)⟩

/-- **The kernel of the structure map of `a ≫ b` is that of `b`** when the structure map of `a` is
a split monomorphism: the structure map of `a ≫ b` is, up to the comparisons of Stacks 03G8, the
structure map of `b` followed by the direct image of that of `a`. -/
theorem fSharp_app_eq_zero_of_comp {X₁ X₂ X : AlgebraicSpaces B S hS} (a : X₁ ⟶ X₂)
    (b : X₂ ⟶ X) (ha : ∃ r, (smallEtaleRingedToposHom B S hS a).fSharp ≫ r = 𝟙 _)
    (c : X₁ ⟶ X) (hc : a ≫ b = c) (U : (SmallEtale B S hS X.1)ᵒᵖ)
    (x : (smallEtaleRingedTopos B S hS X).O.obj.obj U)
    (hx : (smallEtaleRingedToposHom B S hS c).fSharp.hom.app U x = 0) :
    (smallEtaleRingedToposHom B S hS b).fSharp.hom.app U x = 0 := by
  subst hc
  obtain ⟨r, hr⟩ := ha
  set F := Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor.{u, u, u, u + 1, u, u + 1}
    (smallEtaleRingedToposHom B S hS b).toToposHom
  have hFr : F.map (smallEtaleRingedToposHom B S hS a).fSharp ≫ F.map r = 𝟙 _ := by
    rw [← F.map_comp, hr, F.map_id]
  have key : ∀ y, (F.map r).hom.app U ((F.map (smallEtaleRingedToposHom B S hS a).fSharp).hom.app U
      y) = y := fun y =>
    ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f ↦ f.hom) hFr) U) y
  have h2 : (F.map (smallEtaleRingedToposHom B S hS a).fSharp).hom.app U
      ((smallEtaleRingedToposHom B S hS b).fSharp.hom.app U x) = 0 := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun f ↦ f.hom)
      (fSharp_comp_compRingIso_inv B S hS a b)) U) x
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, CommRingCat.hom_comp,
      RingHom.comp_apply, hx, map_zero] at h
    exact h.symm
  exact (key _).symm.trans ((congrArg (ConcreteCategory.hom ((F.map r).hom.app U)) h2).trans
    (map_zero _))

/-- **A first order thickening of algebraic spaces is a first order thickening of small étale
ringed topoi** (the first-order half of the content of Stacks 0D16, registered elsewhere).
Let `i : Z ⟶ Z'` identify `Z` with its range, a first order thickening of `Z'` (Stacks 05ZK). Then
`(Z_étale, 𝒪_Z) ⟶ (Z'_étale, 𝒪_{Z'})` is a first order thickening of ringed topoi (Stacks 08M7):
its direct image is an equivalence (Stacks 05ZJ), its structure map is surjective (`i` is a closed
immersion), and the kernel of the structure map is the defining ideal of the range, which has
square zero. -/
theorem isFirstOrderThickening_smallEtaleRingedToposHom {Z Z' : AlgebraicSpaces B S hS}
    (i : Z ⟶ Z') (hiso : IsIso (Subfunctor.toRange i.hom))
    (hfo : IsFirstOrderThickening B S hS Z' (Subfunctor.range i.hom)) :
    Deformation.ToposThickening.IsFirstOrderThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i) := by
  obtain ⟨hG, hsq⟩ := hfo
  have hi : IsThickeningHom B S hS i := ⟨hiso, hG⟩
  have hψφ := homMk_inv_comp_homMk_toRange B S hS i hi
  have hret := exists_retraction_fSharp B S hS
    (ObjectProperty.homMk (Subfunctor.toRange i.hom) : Z ⟶ IsThickening.space B S hS hG) _ hψφ
  have hker : ∀ (U : (SmallEtale B S hS Z'.1)ᵒᵖ)
      (x : (smallEtaleRingedTopos B S hS Z').O.obj.obj U),
      (smallEtaleRingedToposHom B S hS i).fSharp.hom.app U x = 0 →
        x ∈ definingIdealAt B S hS Z' ⟨Subfunctor.range i.hom, hG.1⟩ U := by
    intro U x hx
    have h0 := fSharp_app_eq_zero_of_comp B S hS _ (IsThickening.inclusion B S hS hG) hret i
      (homMk_toRange_comp_inclusion B S hS i hi) U x hx
    show ((structureSharp B S hS (IsThickening.inclusion B S hS hG)).hom.app U).hom x = 0
    rw [← map_structureSharpCommRing]
    exact h0
  have hzero : ∀ (U : (SmallEtale B S hS Z'.1)ᵒᵖ)
      (a b : (smallEtaleRingedTopos B S hS Z').O.obj.obj U),
      (smallEtaleRingedToposHom B S hS i).fSharp.hom.app U a = 0 →
        (smallEtaleRingedToposHom B S hS i).fSharp.hom.app U b = 0 → a * b = 0 := by
    intro U a b ha hb
    have hpow2 := hsq U.unop
    rw [Submodule.pow_succ, Submodule.pow_one] at hpow2
    have hmul : definingIdealAt B S hS Z' ⟨Subfunctor.range i.hom, hG.1⟩ U *
        definingIdealAt B S hS Z' ⟨Subfunctor.range i.hom, hG.1⟩ U = ⊥ := hpow2
    exact (Submodule.eq_bot_iff _).mp hmul _ (Ideal.mul_mem_mul (hker U a ha) (hker U b hb))
  refine ⟨⟨isEquivalence_smallToposMorphismTypeU_pushforward_of_isThickeningHom B S hS i hi,
    ?_, fun U a ha => ⟨⊤, (smallEtaleRingedTopos B S hS Z').J.top_mem _, fun V p _ => ⟨2, ?_⟩⟩⟩,
    hzero⟩
  · have h := isLocallySurjective_structureSharp B S hS i hi.isClosedImmersion
    rw [← map_structureSharpCommRing] at h
    exact ⟨fun {_} s => h.imageSieve_mem s⟩
  · have haa : a * a = 0 := hzero U a a ha ha
    rw [pow_two, ← map_mul, haa, map_zero]

/-- **The first order thickening of small étale ringed topoi of a first order thickening of
algebraic spaces**, with its square-zero ideal (Stacks 08MB); see
`AlgebraicGeometry.Space.isFirstOrderThickening_smallEtaleRingedToposHom`. -/
noncomputable def smallEtaleRingedToposHomFirstOrderThickening {Z Z' : AlgebraicSpaces B S hS}
    (i : Z ⟶ Z') (hiso : IsIso (Subfunctor.toRange i.hom))
    (hfo : IsFirstOrderThickening B S hS Z' (Subfunctor.range i.hom)) :
    Deformation.ToposThickening.FirstOrderThickening.{u, u + 1, u, u, u + 1, u}
      (smallEtaleRingedToposHom B S hS i) :=
  Deformation.ToposThickening.FirstOrderThickening.ofIsFirstOrderThickening.{u, u + 1, u, u, u + 1}
    (isFirstOrderThickening_smallEtaleRingedToposHom B S hS i hiso hfo)

end AlgebraicGeometry.Space

end
