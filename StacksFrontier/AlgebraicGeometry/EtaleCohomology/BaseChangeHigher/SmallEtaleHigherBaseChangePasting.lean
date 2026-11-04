module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyCompatible
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusSingleCompatible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleDerivedPasting

/-!
# Pasting of the base change map on higher direct images of abelian small étale sheaves

For two horizontally composable commutative squares of schemes

```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
v           v          v
S₂ --u₂--> S₁ --u₁--> S₀
```

the base change map of [Stacks, Tag 0F02] on higher direct images,
`Stacks.EtaleCohomology.higherBaseChangeMapAb`, of the outer rectangle in degree `q` is the
composite of the base change maps of the two squares, read through the composition comparisons
`Stacks.EtaleCohomology.smallEtalePullbackAbCompIso` of the inverse images along the two
composite horizontal legs `u₂ ≫ u₁` and `v₂ ≫ v₁`.

The degree-`q` base change map is the degree-`q` cohomology of the derived comparison
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, read through the two identifications
`Stacks.EtaleCohomology.baseChangeSourceIso` and
`Stacks.EtaleCohomology.baseChangeTargetIso`, so the pasting law in degree `q` is the
derived pasting law `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app`
read through those two identifications.

## Main definitions

* `Stacks.DerivedFunctor.HomologyCompatible` and `Stacks.DerivedFunctor.SingleCompatible`: the
  two cocycle identities of the comparisons, as predicates on an isomorphism
  `U₁ ⋙ U₂ ≅ U` of exact functors.

## Main results

* `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_derived`: the pasting law read through
  the two identifications, with the derived composite on the right.
* `Stacks.EtaleCohomology.higherBaseChangeMapAb_paste_app`: the pasting law for the base
  change map on higher direct images, with the two composition comparisons of inverse images
  on the two sides. Its only hypotheses are the commutativity of the two squares.
* `Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_paste`: if the degree-`q` base
  change maps of the two squares are isomorphisms, so is the one of the outer rectangle.
* `Stacks.EtaleCohomology.source_paste`, `Stacks.EtaleCohomology.middle_paste`,
  `Stacks.EtaleCohomology.target_paste`: the identifications of the rectangle and of the two
  squares exchange along the comparisons of the inverse images.
* `Stacks.DerivedFunctor.homologyCompatible` and `Stacks.DerivedFunctor.singleCompatible`: the
  two cocycle identities, for arbitrary exact functors.

## Implementation notes

`Stacks.EtaleCohomology.baseChangeSourceIso` is built from the comparison
`H^q(R(f')⁻¹K) ≅ (f')⁻¹H^q(K)` of an exact functor with cohomology,
`Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso`, and
`Stacks.EtaleCohomology.baseChangeTargetIso` from the comparison `e⁻¹(F[0]) ≅ (Re⁻¹)(F[0])`,
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso`. The rectangle's identifications
use those comparisons for the composite legs, the squares' use them for the individual legs, so
the pasting law uses that each comparison is compatible with a composition of exact functors,
read through `CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`. Those two cocycle
identities are `Stacks.DerivedFunctor.HomologyCompatible` and
`Stacks.DerivedFunctor.SingleCompatible`, statements about an isomorphism `U₁ ⋙ U₂ ≅ U` of exact
functors between abelian categories with enough injectives, proved in that generality by
`Stacks.DerivedFunctor.homologyCompatible` and `Stacks.DerivedFunctor.singleCompatible`.

## References

* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZS](https://stacks.math.columbia.edu/tag/0EZS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.DerivedFunctor

/-! ### The two cocycle identities of the comparisons with a composition of exact functors -/

section Comp

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  [Abelian C₀] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [EnoughInjectives C₀] [EnoughInjectives C₁]
  (U₁ : C₀ ⥤ C₁) (U₂ : C₁ ⥤ C₂) (U : C₀ ⥤ C₂)
  [U₁.Additive] [U₂.Additive] [U.Additive]
  [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
  [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
  [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (c : U₁ ⋙ U₂ ≅ U)

/-- **The compatibility of the cohomology comparison of an exact functor with a composition.**
For exact `U₁`, `U₂`, `U` and an isomorphism `c : U₁ ⋙ U₂ ≅ U`, the comparison
`H^n ∘ U ≅ RU ∘ H^n` of `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` for `U`, read
through the comparison `RU₁ ⋙ RU₂ ≅ RU` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`, is the composite of the
comparisons for `U₁` and for `U₂`, read through `c`. -/
def HomologyCompatible (n : ℤ) : Prop :=
  (exactRightDerivedPlusHomologyIso U n).inv ≫
      Functor.whiskerRight (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).inv
        (DerivedCategory.Plus.homologyFunctor C₂ n) =
    Functor.whiskerLeft (DerivedCategory.Plus.homologyFunctor C₀ n) c.inv ≫
      Functor.whiskerRight (exactRightDerivedPlusHomologyIso U₁ n).inv U₂ ≫
        Functor.whiskerLeft U₁.rightDerivedFunctorPlus
          (exactRightDerivedPlusHomologyIso U₂ n).inv

/-- **The compatibility of the degree-zero embedding comparison of an exact functor with a
composition.** For exact `U₁`, `U₂`, `U` and an isomorphism `c : U₁ ⋙ U₂ ≅ U`, the comparison
`U(X)[0] ≅ RU(X[0])` of `Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` for `U`,
precomposed with `c`, is the composite of the comparisons for `U₁` and for `U₂`, read through
the comparison `RU₁ ⋙ RU₂ ≅ RU` of
`CategoryTheory.Functor.rightDerivedFunctorPlusCompIsoOfExact`. -/
def SingleCompatible : Prop :=
  ∀ Y : C₀,
    (DerivedCategory.Plus.singleFunctor C₂ 0).map (c.hom.app Y) ≫
        (exactSingleFunctorRightDerivedPlusIso U 0).hom.app Y =
      (exactSingleFunctorRightDerivedPlusIso U₂ 0).hom.app (U₁.obj Y) ≫
        U₂.rightDerivedFunctorPlus.map
            ((exactSingleFunctorRightDerivedPlusIso U₁ 0).hom.app Y) ≫
          (Functor.rightDerivedFunctorPlusCompIsoOfExact U₁ U₂ U c).hom.app
            ((DerivedCategory.Plus.singleFunctor C₀ 0).obj Y)

/-- **The cohomology comparison of an exact functor is compatible with a composition.** -/
theorem homologyCompatible (n : ℤ) : HomologyCompatible U₁ U₂ U c n :=
  exactRightDerivedPlusHomologyIso_comp U₁ U₂ U c n

/-- **The degree-zero embedding comparison of an exact functor is compatible with a
composition.** -/
theorem singleCompatible : SingleCompatible U₁ U₂ U c := fun Y =>
  exactSingleFunctorRightDerivedPlusIso_comp U₁ U₂ U c Y

end Comp

end Stacks.DerivedFunctor

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### The rearrangements, on variables -/

private theorem paste_chain {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : E}
    {x : o₁ ⟶ o₂} {ρ : o₂ ⟶ o₃} {m : o₃ ⟶ o₇} {ρ' : o₁ ⟶ o₄} {n : o₄ ⟶ o₃}
    {m₁ : o₄ ⟶ o₅} {m₂ : o₅ ⟶ o₆} {m₃ : o₆ ⟶ o₇}
    (h₁ : x ≫ ρ = ρ' ≫ n) (h₂ : n ≫ m = m₁ ≫ m₂ ≫ m₃) :
    x ≫ ρ ≫ m = (ρ' ≫ m₁) ≫ m₂ ≫ m₃ := by
  rw [← Category.assoc x, h₁, Category.assoc, h₂, Category.assoc]

private theorem paste_source {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ o₆ o₇ : E}
    {p : o₁ ⟶ o₂} {A : o₂ ⟶ o₃} {B : o₃ ⟶ o₇} {d : o₂ ⟶ o₄} {y : o₄ ⟶ o₅} {t : o₅ ⟶ o₇}
    {cinv : o₁ ⟶ o₆} {x : o₆ ⟶ o₄} {W : o₆ ⟶ o₅}
    (h₁ : A ≫ B = d ≫ y ≫ t) (h₂ : p ≫ d = cinv ≫ x) (h₃ : W = x ≫ y) :
    (p ≫ A) ≫ B = cinv ≫ W ≫ t := by
  rw [h₃, Category.assoc, h₁, ← Category.assoc p, h₂]
  simp

private theorem paste_mid {E : Type*} [Category* E] {o₁ o₂ o₃ o₄ o₅ : E}
    {u : o₁ ⟶ o₂} {A : o₂ ⟶ o₃} {B : o₃ ⟶ o₄} {y : o₂ ⟶ o₅} {C : o₅ ⟶ o₄} {W : o₁ ⟶ o₅}
    (h₁ : A ≫ B = y ≫ C) (h₂ : W = u ≫ y) :
    (u ≫ A) ≫ B = W ≫ C := by
  rw [h₂, Category.assoc, h₁, Category.assoc]

/-- The rearrangement of the seven squares of the transport into the pasting identity. -/
private theorem paste_main {E : Type*} [Category* E]
    {o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 o14 : E}
    {x : o1 ⟶ o2} {B₁ : o2 ⟶ o3} {bc2 : o3 ⟶ o4} {z : o4 ⟶ o5} {T : o5 ⟶ o6}
    {So : o1 ⟶ o7} {Habcd : o7 ⟶ o6}
    {t2 : o4 ⟶ o8} {p : o8 ⟶ o9} {hd : o9 ⟶ o6}
    {s2 : o3 ⟶ o10} {hD2S : o10 ⟶ o8} {hσ : o10 ⟶ o11} {hc : o11 ⟶ o9}
    {U₂t1 : o3 ⟶ o12} {th : o12 ⟶ o11} {U₂s1 : o2 ⟶ o13} {U₂hD1 : o13 ⟶ o12}
    {th' : o13 ⟶ o14} {hb : o14 ⟶ o11} {ha : o7 ⟶ o14}
    (h4 : z ≫ T = t2 ≫ p ≫ hd) (h2 : s2 ≫ hD2S = bc2 ≫ t2)
    (h7 : hD2S ≫ p = hσ ≫ hc) (h5' : s2 ≫ hσ = U₂t1 ≫ th)
    (hB : B₁ ≫ U₂t1 = U₂s1 ≫ U₂hD1) (h5 : U₂hD1 ≫ th = th' ≫ hb)
    (h3 : So ≫ ha = x ≫ U₂s1 ≫ th') (h8 : Habcd = ha ≫ hb ≫ hc ≫ hd) :
    (x ≫ B₁ ≫ bc2 ≫ z) ≫ T = So ≫ Habcd := by
  rw [h8]
  simp only [Category.assoc]
  rw [h4, reassoc_of% h2.symm, reassoc_of% h7, reassoc_of% h5', reassoc_of% hB,
    reassoc_of% h5, ← reassoc_of% h3]

/-! ### The components of the two identifications -/

section Components

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (q : ℕ)

/-- The identification of `(f')⁻¹ R^q g_*` with cohomology of the derived source, at a sheaf:
the comparison of the two conventions for the right derived functor of `g_*`, followed by the
comparison of the exact functor `(f')⁻¹` with cohomology. -/
public theorem baseChangeSourceIso_hom_app (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (baseChangeSourceIso f' g q).hom.app F =
      (smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.app F) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
            (smallEtalePullbackAb f') (q : ℤ)).inv.app
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj F)) := rfl

/-- The identification of `R^q h_* e⁻¹` with cohomology of the derived target, at a sheaf: the
comparison of the two conventions for the right derived functor of `h_*`, followed by the
comparison of the exact functor `e⁻¹` with the degree-zero embedding. -/
public theorem baseChangeTargetIso_hom_app (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (baseChangeTargetIso h e q).hom.app F =
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q).hom.app
          ((smallEtalePullbackAb e).obj F) ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology X') Ab.{u + 1}) (q : ℤ)).map
          ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb e) 0).hom.app F)) := rfl

end Components

/-- The comparison of the derived inverse images along a composite is the generic comparison for
an isomorphism of exact functors, at the composition isomorphism of the inverse images. -/
public theorem smallEtaleDerivedPullbackAbPlusCompIso_eq {A B C : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) :
    smallEtaleDerivedPullbackAbPlusCompIso a b =
      Functor.rightDerivedFunctorPlusCompIsoOfExact (smallEtalePullbackAb b)
        (smallEtalePullbackAb a) (smallEtalePullbackAb (a ≫ b))
        (smallEtalePullbackAbCompIso a b) := rfl

/-! ### The three transport steps -/

section Paste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}}

/-- Naturality of the derived base change comparison of the second square at the comparison for
`v₁`, read in degree `q` cohomology. -/
private theorem homology_map_derivedBaseChange_naturality (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
    (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
        ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
          ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb v₁) 0).hom.app F))) ≫
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
        ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
          ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) =
    (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
        ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) 0).obj
              ((smallEtalePullbackAb v₁).obj F))) ≫
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
        ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
          ((smallEtalePullbackAb v₂).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb v₁) 0).hom.app F))) := by
  simpa only [Functor.comp_obj, Functor.comp_map, Functor.map_comp] using
    congrArg (DerivedCategory.Plus.homologyFunctor
        (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
      ((smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).naturality
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (smallEtalePullbackAb v₁) 0).hom.app F))

/-- **The source side of the transport.** The identification of the rectangle's source,
followed by the cohomology of the comparison of the derived inverse images along `u₂ ≫ u₁`, is
the composition comparison of the inverse images along `u₂ ≫ u₁` followed by the inverse image
along `u₂` of the identification of the first square's source. -/
public theorem source_paste (g₀ : X₀ ⟶ S₀) (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (baseChangeSourceIso (u₂ ≫ u₁) g₀ q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
          ((smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv.app
            ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) =
      (smallEtalePullbackAbCompIso u₂ u₁).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj F) ≫
        (smallEtalePullbackAb u₂).map ((baseChangeSourceIso u₁ g₀ q).hom.app F) ≫
          (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
              (smallEtalePullbackAb u₂) (q : ℤ)).inv.app
            ((smallEtalePullbackAb u₁).rightDerivedFunctorPlus.obj
              ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) := by
  have hG1 := NatTrans.congr_app
    (Stacks.DerivedFunctor.homologyCompatible (smallEtalePullbackAb u₁)
      (smallEtalePullbackAb u₂) (smallEtalePullbackAb (u₂ ≫ u₁))
      (smallEtalePullbackAbCompIso u₂ u₁) (q : ℤ))
    ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hG1
  have hnat : (smallEtalePullbackAb (u₂ ≫ u₁)).map
        ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₀) q).hom.app F) ≫
      (smallEtalePullbackAbCompIso u₂ u₁).inv.app
        ((DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S₀) Ab.{u + 1}) (q : ℤ)).obj
          ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) =
      (smallEtalePullbackAbCompIso u₂ u₁).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj F) ≫
        (smallEtalePullbackAb u₂).map ((smallEtalePullbackAb u₁).map
          ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₀) q).hom.app F)) :=
    (smallEtalePullbackAbCompIso u₂ u₁).inv.naturality _
  rw [baseChangeSourceIso_hom_app, baseChangeSourceIso_hom_app,
    smallEtaleDerivedPullbackAbPlusCompIso_eq]
  exact paste_source hG1 hnat ((smallEtalePullbackAb u₂).map_comp _ _)

/-- **The middle of the transport.** The identification of the first square's target, read
through the inverse image along `u₂`, and the identification of the second square's source are
exchanged by the comparison of the inverse image along `u₂` with cohomology. -/
public theorem middle_paste (g₁ : X₁ ⟶ S₁) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (baseChangeSourceIso u₂ g₁ q).hom.app ((smallEtalePullbackAb v₁).obj F) ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
          ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
            ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map
              ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
                (smallEtalePullbackAb v₁) 0).hom.app F))) =
      (smallEtalePullbackAb u₂).map ((baseChangeTargetIso g₁ v₁ q).hom.app F) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
            (smallEtalePullbackAb u₂) (q : ℤ)).inv.app
          ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.obj
            ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) := by
  have hnat : (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
          (smallEtalePullbackAb u₂) (q : ℤ)).inv.app
        ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (smallEtaleTopology X₁) Ab.{u + 1}) 0).obj
              ((smallEtalePullbackAb v₁).obj F))) ≫
      (DerivedCategory.Plus.homologyFunctor
          (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
        ((smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
          ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb v₁) 0).hom.app F))) =
      (smallEtalePullbackAb u₂).map
          ((DerivedCategory.Plus.homologyFunctor
              (Sheaf (smallEtaleTopology S₁) Ab.{u + 1}) (q : ℤ)).map
            ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map
              ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
                (smallEtalePullbackAb v₁) 0).hom.app F))) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
            (smallEtalePullbackAb u₂) (q : ℤ)).inv.app
          ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.obj
            ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor
                (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) :=
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb u₂) (q : ℤ)).inv.naturality
      ((smallEtalePushforwardAb g₁).rightDerivedFunctorPlus.map
        ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
          (smallEtalePullbackAb v₁) 0).hom.app F))).symm
  rw [baseChangeSourceIso_hom_app, baseChangeTargetIso_hom_app]
  exact paste_mid hnat ((smallEtalePullbackAb u₂).map_comp _ _)

/-- **The target side of the transport.** The composition comparison of the inverse images
along `v₂ ≫ v₁`, pushed forward and followed by the identification of the rectangle's target,
is the identification of the second square's target followed by the cohomology of the
comparison of the derived inverse images along `v₂ ≫ v₁`. -/
public theorem target_paste (g₂ : X₂ ⟶ S₂) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    ((smallEtalePushforwardAb g₂).rightDerived q).map
          ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F) ≫
        (baseChangeTargetIso g₂ (v₂ ≫ v₁) q).hom.app F =
      (baseChangeTargetIso g₂ v₂ q).hom.app ((smallEtalePullbackAb v₁).obj F) ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
          ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
            ((smallEtalePullbackAb v₂).rightDerivedFunctorPlus.map
              ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
                (smallEtalePullbackAb v₁) 0).hom.app F))) ≫
          (DerivedCategory.Plus.homologyFunctor
              (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
            ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
              ((smallEtaleDerivedPullbackAbPlusCompIso v₂ v₁).hom.app
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) := by
  have hnat : ((smallEtalePushforwardAb g₂).rightDerived q).map
        ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F) ≫
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₂) q).hom.app
        ((smallEtalePullbackAb (v₂ ≫ v₁)).obj F) =
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₂) q).hom.app
          ((smallEtalePullbackAb v₂).obj ((smallEtalePullbackAb v₁).obj F)) ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
          ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) 0).map
                ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F))) :=
    (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g₂) q).hom.naturality _
  have h₂ := congrArg (fun z => (DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
        ((smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map z))
    (Stacks.DerivedFunctor.singleCompatible (smallEtalePullbackAb v₁)
      (smallEtalePullbackAb v₂) (smallEtalePullbackAb (v₂ ≫ v₁))
      (smallEtalePullbackAbCompIso v₂ v₁) F)
  simp only [Functor.map_comp] at h₂
  rw [baseChangeTargetIso_hom_app, baseChangeTargetIso_hom_app,
    smallEtaleDerivedPullbackAbPlusCompIso_eq]
  exact paste_chain hnat h₂

/-! ### The pasting law -/

/-- **The pasting law for the base change map on higher direct images, read through the two
identifications.** The base change map of the outer rectangle, followed by the identification
of its target, is the identification of its source followed by the degree-`q` cohomology of the
composite of the two derived base change comparisons. -/
public theorem higherBaseChangeMapAb_paste_derived (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
    (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
            (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F ≫
        (baseChangeTargetIso g₂ (v₂ ≫ v₁) q).hom.app F =
      (baseChangeSourceIso (u₂ ≫ u₁) g₀ q).hom.app F ≫
        (DerivedCategory.Plus.homologyFunctor
            (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
          ((smallEtaleDerivedPullbackAbPlusCompIso u₂ u₁).inv.app
              ((smallEtalePushforwardAb g₀).rightDerivedFunctorPlus.obj
                ((DerivedCategory.Plus.singleFunctor
                  (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F)) ≫
            (smallEtalePullbackAb u₂).rightDerivedFunctorPlus.map
                ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
                  ((DerivedCategory.Plus.singleFunctor
                    (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F)) ≫
              (smallEtaleDerivedBaseChangeAb u₂ g₁ g₂ v₂ w₂).app
                  ((smallEtalePullbackAb v₁).rightDerivedFunctorPlus.obj
                    ((DerivedCategory.Plus.singleFunctor
                      (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F)) ≫
                (smallEtalePushforwardAb g₂).rightDerivedFunctorPlus.map
                  ((smallEtaleDerivedPullbackAbPlusCompIso v₂ v₁).hom.app
                    ((DerivedCategory.Plus.singleFunctor
                      (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))) := by
  rw [← baseChangeSourceIso_hom_app_comp (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
    (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q F,
    smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂]

/-- **The pasting law for the base change map on higher direct images.** For two horizontally
composable commutative squares of schemes, the base change map of the outer rectangle in degree
`q` is the composite of the base change maps of the two squares, read through the composition
comparisons of the inverse images along the two composite horizontal legs.

The hypotheses are the commutativity of the two squares and nothing else: the squares need not
be cartesian, and no finiteness, separatedness or torsion condition enters. -/
public theorem higherBaseChangeMapAb_paste_app (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
    (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F =
      (smallEtalePullbackAbCompIso u₂ u₁).inv.app
          (((smallEtalePushforwardAb g₀).rightDerived q).obj F) ≫
        (smallEtalePullbackAb u₂).map
            ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F) ≫
          (higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app ((smallEtalePullbackAb v₁).obj F) ≫
            ((smallEtalePushforwardAb g₂).rightDerived q).map
              ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F) := by
  have bridge₁ := baseChangeSourceIso_hom_app_comp u₁ g₀ g₁ v₁ w₁ q F
  have bridge₂ := baseChangeSourceIso_hom_app_comp u₂ g₁ g₂ v₂ w₂ q
    ((smallEtalePullbackAb v₁).obj F)
  have bridgeOut := baseChangeSourceIso_hom_app_comp (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
    (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q F
  have h4 := target_paste g₂ v₁ v₂ q F
  have h3 := source_paste g₀ u₁ u₂ q F
  have h5' := middle_paste g₁ u₂ v₁ q F
  have hB := congrArg (smallEtalePullbackAb u₂).map bridge₁.symm
  simp only [Functor.map_comp] at hB
  have h5 := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb u₂) (q : ℤ)).inv.naturality
    ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))
  have h7 := (homology_map_derivedBaseChange_naturality g₁ g₂ u₂ v₁ v₂ w₂ q F).symm
  have h8 := congrArg (DerivedCategory.Plus.homologyFunctor
      (Sheaf (smallEtaleTopology S₂) Ab.{u + 1}) (q : ℤ)).map
    (smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))
  simp only [Functor.map_comp] at h8
  have key := paste_main h4 bridge₂ h7 h5' hB h5 h3 h8
  exact ((cancel_mono ((baseChangeTargetIso g₂ (v₂ ≫ v₁) q).hom.app F)).mp
    (key.trans bridgeOut)).symm

/-! ### Invertibility of the base change map of the rectangle -/

/-- **Base change maps of a rectangle of squares.** Consider a tower of two commutative squares
of schemes
```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
v           v          v
S₂ --u₂--> S₁ --u₁--> S₀
```
written in the notation of the Stacks Project by `u₁ = f`, `v₁ = e`, `g₀ = g`, `g₁ = h`,
`u₂ = i`, `v₂ = k`, `g₂ = j`, let `F` be an abelian sheaf on the small étale site of `X₀` and let
`q` be a degree.
If the degree-`q` base change maps `f⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of the lower square and
`i⁻¹ R^q h_* (e⁻¹ F) ⟶ R^q j_* k⁻¹ (e⁻¹ F)` of the upper square are isomorphisms, then so is the
degree-`q` base change map `(i ≫ f)⁻¹ R^q g_* F ⟶ R^q j_* (k ≫ e)⁻¹ F` of the outer rectangle.
Nothing is assumed of the squares beyond commutativity: neither need be cartesian, and the
degree `q` is arbitrary — each degree is a separate statement, with the same degree in the
hypotheses and in the conclusion. -/
@[stacks 0EZS "the abelian half: for an abelian sheaf F on T_étale and a degree q, if \
f⁻¹R^qg_*F → R^qh_*e⁻¹F and i⁻¹R^qh_*e⁻¹F → R^qj_*k⁻¹e⁻¹F are isomorphisms then \
(f∘i)⁻¹R^qg_*F → R^qj_*(e∘k)⁻¹F is an isomorphism; the derived statement of the same tag is \
`etaleAbelianDerivedBaseChange_isIso_of_comp`"]
public theorem isIso_higherBaseChangeMapAb_app_of_paste (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁)
    (g₂ : X₂ ⟶ S₂) (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
    (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁) (q : ℕ)
    (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1})
    (h₁ : IsIso ((higherBaseChangeMapAb u₁ g₀ g₁ v₁ w₁ q).app F))
    (h₂ : IsIso ((higherBaseChangeMapAb u₂ g₁ g₂ v₂ w₂ q).app
      ((smallEtalePullbackAb v₁).obj F))) :
    IsIso ((higherBaseChangeMapAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
      (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) q).app F) := by
  rw [isIso_higherBaseChangeMapAb_app_iff] at h₁ h₂ ⊢
  have hnatB := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (smallEtalePullbackAb u₂) (q : ℤ)).hom.naturality
    ((smallEtaleDerivedBaseChangeAb u₁ g₀ g₁ v₁ w₁).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) 0).obj F))
  have hnatC := homology_map_derivedBaseChange_naturality g₁ g₂ u₂ v₁ v₂ w₂ q F
  simp only [Functor.comp_obj, Functor.comp_map] at hnatB
  have hB := IsIso.of_isIso_fac_right hnatB
  have hC := IsIso.of_isIso_fac_left hnatC
  rw [smallEtaleDerivedBaseChangeAb_eq_derivedPaste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂]
  simp only [Functor.map_comp]
  infer_instance

end Paste

end Stacks.EtaleCohomology

end
