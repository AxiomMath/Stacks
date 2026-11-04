module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Adjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Extension by zero along a composite of étale morphisms

Let `U` be an object of the small étale site of `X` and `V` an object of the small étale site of
`U`. Composing with `U ⟶ X` makes `V` an object of the small étale site of `X`, and the three
restriction functors satisfy `j_V^{-1} ∘ j_U^{-1} = j_{V∘U}^{-1}` up to the canonical comparison;
passing to left adjoints gives `j_{U!} ∘ j_{V!} ≅ j_{(V∘U)!}` on sheaves of modules.

## Main definitions

* `AlgebraicGeometry.smallEtaleCompObject`: `V` as an object of the small étale site of `X`,
  through the composite of its structure morphism with that of `U`.
* `AlgebraicGeometry.smallEtalePostcomposeCompIso`: composing with `V ⟶ U` and then with
  `U ⟶ X` is composing with the composite, as functors of small étale sites.
* `AlgebraicGeometry.moduleRestrictionCompIso`: the identification of the composite of the two
  restrictions with the restriction along the composite.
* `AlgebraicGeometry.moduleExtensionByZeroCompIso`: `j_{U!} ∘ j_{V!} ≅ j_{(V∘U)!}` for sheaves
  of modules.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) (V : SmallEtale B U.obj.left.1 U.obj.left.property)

/-- **An étale object of an étale object is an étale object.** The object of the small étale site
of `X` attached to an object `V` of the small étale site of `U`: the same scheme, with the
composite of the two structure morphisms, which is étale because both are. -/
public abbrev smallEtaleCompObject : SmallEtale B X hX :=
  ⟨{ left := V.obj.left, right := ⟨⟨⟩⟩, hom := V.obj.hom ≫ U.obj.hom },
    B.etale_map_comp V.obj.hom U.obj.hom V.property U.property⟩

/-- **Composition with étale morphisms is associative.** Composing with `V ⟶ U` and then with
`U ⟶ X` is composing with the composite `V ⟶ X`, as functors from the small étale site of `V` to
the small étale site of `X`. Each component is the identity on the underlying scheme. -/
public def smallEtalePostcomposeCompIso :
    smallEtalePostcompose B U.obj.left.1 U.obj.left.property V ⋙
        smallEtalePostcompose B X hX U ≅
      smallEtalePostcompose B X hX (smallEtaleCompObject B X hX U V) :=
  NatIso.ofComponents
    (fun W ↦ (BigEtaleOver.IsEtaleOver B X hX).fullyFaithfulι.preimageIso
      (Over.isoMk (Iso.refl _) (by
        change 𝟙 _ ≫ W.obj.hom ≫ V.obj.hom ≫ U.obj.hom =
          (W.obj.hom ≫ V.obj.hom) ≫ U.obj.hom
        simp only [Category.id_comp, Category.assoc])))
    (by
      intro W₁ W₂ f
      apply ObjectProperty.hom_ext
      apply Over.OverMorphism.ext
      change f.hom.left ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.left
      simp only [Category.comp_id, Category.id_comp])

variable (Λ : Type v) [Ring Λ]

/-- **Restriction of sheaves of modules composes.** Restricting from `X` to `U` and then from `U`
to `V` is restricting from `X` to the composite `V ⟶ X`. -/
public def moduleRestrictionCompIso :
    moduleRestriction.{u, v, max (u + 1) v} B X hX U Λ ⋙
        moduleRestriction.{u, v, max (u + 1) v} B U.obj.left.1 U.obj.left.property V Λ ≅
      moduleRestriction.{u, v, max (u + 1) v} B X hX (smallEtaleCompObject B X hX U V) Λ :=
  Functor.sheafPushforwardContinuousComp' (smallEtalePostcomposeCompIso B X hX U V)
    (ModuleCat.{max (u + 1) v} Λ)
    (SmallEtale.topology B V.obj.left.1 V.obj.left.property)
    (SmallEtale.topology B U.obj.left.1 U.obj.left.property)
    (SmallEtale.topology B X hX)

/-- **Extension by zero of sheaves of modules composes.** Extending by zero from `V` to `U` and
then from `U` to `X` is extending by zero from the composite `V ⟶ X`: the two functors are left
adjoint to the two sides of `AlgebraicGeometry.moduleRestrictionCompIso`. -/
public def moduleExtensionByZeroCompIso :
    moduleExtensionByZero B U.obj.left.1 U.obj.left.property V Λ ⋙
        moduleExtensionByZero B X hX U Λ ≅
      moduleExtensionByZero B X hX (smallEtaleCompObject B X hX U V) Λ :=
  Adjunction.leftAdjointUniq
    (((moduleExtensionByZeroAdjunction B U.obj.left.1 U.obj.left.property V Λ).comp
        (moduleExtensionByZeroAdjunction B X hX U Λ)).ofNatIsoRight
      (moduleRestrictionCompIso B X hX U V Λ))
    (moduleExtensionByZeroAdjunction B X hX (smallEtaleCompObject B X hX U V) Λ)

end AlgebraicGeometry

end
