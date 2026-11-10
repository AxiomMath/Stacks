module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityInvariance

/-!
# The relative property of Stacks 03YK is an invariant of a square of equivalences

Let `S` be an object of a big fppf site and let `P` be a property of morphisms of algebraic spaces
over `S` as in [Stacks, Tag 03YK]. In a 2-commutative square

```
𝒳' ⟶ 𝒳
f'↓     ↓f
𝒴' ⟶ 𝒴
```

of categories fibred in groupoids over `(Sch/S)_fppf` whose horizontal 1-morphisms are
equivalences and whose vertical 1-morphisms are representable by algebraic spaces, `f` has `P` if
and only if `f'` has `P`.

## Main definitions

* `AlgebraicGeometry.Stack.inverseTwoCommSqIso`: the 2-commutativity isomorphism of the square
  obtained by inverting both horizontal equivalences.

## Main results

* `AlgebraicGeometry.Stack.hasRelativeProperty_iff_of_equivalences`: `f` has `P` if and only if
  `f'` has `P`.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 0459](https://stacks.math.columbia.edu/tag/0459)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v₁ v₂ w₁ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳' 𝒴' : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒳 𝒴 : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- The 2-commutativity isomorphism of the square obtained from a 2-commutative square of
categories fibred in groupoids by inverting both horizontal equivalences.

Given `α : a ⋙ f ≅ f' ⋙ b` with quasi-inverses `aInv` of `a` and `bInv` of `b` over the site,
witnessed by a counit `εa : aInv ⋙ a ≅ 𝟭` and a unit `ηb : b ⋙ bInv ≅ 𝟭`, this is the composite
`aInv ⋙ f' ≅ aInv ⋙ f' ⋙ b ⋙ bInv ≅ aInv ⋙ a ⋙ f ⋙ bInv ≅ f ⋙ bInv`. -/
def inverseTwoCommSqIso
    (f' : 𝒳'.val ⥤ᵇ 𝒴'.val) (f : 𝒳.val ⥤ᵇ 𝒴.val)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f ≅ BasedFunctor.comp f' b)
    {aInv : 𝒳.val.obj ⥤ 𝒳'.val.obj} {bInv : 𝒴.val.obj ⥤ 𝒴'.val.obj}
    (εa : aInv ⋙ a.toFunctor ≅ 𝟭 𝒳.val.obj)
    (ηb : b.toFunctor ⋙ bInv ≅ 𝟭 𝒴'.val.obj) :
    aInv ⋙ f'.toFunctor ≅ f.toFunctor ⋙ bInv :=
  Functor.isoWhiskerLeft (aInv ⋙ f'.toFunctor) ηb.symm ≪≫
    Functor.isoWhiskerLeft aInv
        (Functor.isoWhiskerRight ((BasedNatTrans.forgetful 𝒳'.val 𝒴.val).mapIso α).symm bInv) ≪≫
      Functor.isoWhiskerRight εa (f.toFunctor ⋙ bInv)

/-- In a 2-commutative square of categories fibred in groupoids over the big fppf site of `S`
whose two horizontal 1-morphisms are equivalences, a vertical 1-morphism representable by
algebraic spaces has the relative property `P` of Stacks 03YK if and only if the other vertical
1-morphism does. Representability of `f'` is deduced from that of `f`. -/
@[stacks 0459 "a vertical 1-morphism of a 2-commutative square whose horizontals are \
equivalences has the relative property exactly when the other vertical one does"]
theorem hasRelativeProperty_iff_of_equivalences
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]
    (f' : 𝒳' ⟶ 𝒴') (f : 𝒳 ⟶ 𝒴)
    (a : 𝒳'.val ⥤ᵇ 𝒳.val) (b : 𝒴'.val ⥤ᵇ 𝒴.val)
    (α : BasedFunctor.comp a f.hom ≅ BasedFunctor.comp f'.hom b)
    [Functor.IsEquivalence a.toFunctor] [Functor.IsEquivalence b.toFunctor]
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom) :
    HasRelativeProperty.{u, v₂, w₂} B S hS P f hf ↔
      HasRelativeProperty.{u, v₁, w₁} B S hS P f'
        ((isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f'.hom f.hom a b α).mp
          hf) := by
  have hf' := (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS f'.hom f.hom a b α).mp hf
  constructor
  · exact hasRelativeProperty_of_equivalences B S hS P f' f a b α hf hf'
  · intro h'
    obtain ⟨aInv, haInv, ηa, εa, -, hεa⟩ :=
      Functor.IsFiberedInGroupoids.isEquivalence_over 𝒳'.val.p 𝒳.val.p
        𝒳'.isFiberedInGroupoids 𝒳.isFiberedInGroupoids a.toFunctor a.w inferInstance
    obtain ⟨bInv, hbInv, ηb, εb, hηb, -⟩ :=
      Functor.IsFiberedInGroupoids.isEquivalence_over 𝒴'.val.p 𝒴.val.p
        𝒴'.isFiberedInGroupoids 𝒴.isFiberedInGroupoids b.toFunctor b.w inferInstance
    let aB : 𝒳.val ⥤ᵇ 𝒳'.val := { toFunctor := aInv, w := haInv }
    let bB : 𝒴.val ⥤ᵇ 𝒴'.val := { toFunctor := bInv, w := hbInv }
    have : Functor.IsEquivalence aInv :=
      (CategoryTheory.Equivalence.mk aInv a.toFunctor εa.symm ηa).isEquivalence_functor
    have : Functor.IsEquivalence bInv :=
      (CategoryTheory.Equivalence.mk bInv b.toFunctor εb.symm ηb).isEquivalence_functor
    let ηbB : BasedFunctor.comp b bB ≅ BasedFunctor.id 𝒴'.val :=
      BasedNatIso.mkNatIso ηb hηb
    let α₀ := (BasedNatTrans.forgetful 𝒳'.val 𝒴.val).mapIso α
    let α' := inverseTwoCommSqIso B S hS f'.hom f.hom a b α εa ηb
    have hbB : ∀ (X : 𝒳.val.obj) {Y Z : 𝒴.val.obj} (g : Y ⟶ Z),
        𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X)) g →
          𝒴'.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X)) (bInv.map g) :=
      fun X _ _ g _ => Functor.isHomLift_map_of_comp_eq hbInv (𝟙 (𝒳.val.p.obj X)) g
    have hα' : ∀ X : 𝒳.val.obj,
        𝒴'.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X)) (α'.hom.app X) := by
      intro X
      have hA : 𝒳'.val.p.obj (aInv.obj X) = 𝒳.val.p.obj X := aB.w_obj X
      have h₁ : 𝒴'.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X))
          (ηb.inv.app (f'.hom.obj (aInv.obj X))) := by
        have h := ηbB.inv.isHomLift' (f'.hom.obj (aInv.obj X))
        rwa [f'.hom.w_obj (aInv.obj X), hA] at h
      have h₂ : 𝒴'.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X))
          (bInv.map (α₀.inv.app (aInv.obj X))) := by
        have h := α.inv.isHomLift' (aInv.obj X)
        rw [hA] at h
        exact hbB X (α₀.inv.app (aInv.obj X)) h
      have h₃ : 𝒴'.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X))
          ((f.hom.toFunctor ⋙ bInv).map (εa.hom.app X)) := by
        have := hεa X
        exact hbB X (f.hom.toFunctor.map (εa.hom.app X))
          (Functor.isHomLift_map_of_comp_eq f.hom.w (𝟙 (𝒳.val.p.obj X)) (εa.hom.app X))
      change 𝒴'.val.p.IsHomLift (𝟙 (𝒳.val.p.obj X))
        (ηb.inv.app (f'.hom.obj (aInv.obj X)) ≫ bInv.map (α₀.inv.app (aInv.obj X)) ≫
          (f.hom.toFunctor ⋙ bInv).map (εa.hom.app X))
      exact @IsHomLift.comp_of_lift_id _ _ _ _ 𝒴'.val.p (𝒳.val.p.obj X) _ _ _
        (ηb.inv.app (f'.hom.obj (aInv.obj X)))
        (bInv.map (α₀.inv.app (aInv.obj X)) ≫
          (f.hom.toFunctor ⋙ bInv).map (εa.hom.app X)) h₁
        (@IsHomLift.comp_of_lift_id _ _ _ _ 𝒴'.val.p (𝒳.val.p.obj X) _ _ _
          (bInv.map (α₀.inv.app (aInv.obj X)))
          ((f.hom.toFunctor ⋙ bInv).map (εa.hom.app X)) h₂ h₃)
    exact hasRelativeProperty_of_equivalences B S hS P f f' aB bB
      (BasedNatIso.mkNatIso α' hα') hf' hf h'

end AlgebraicGeometry.Stack

end
