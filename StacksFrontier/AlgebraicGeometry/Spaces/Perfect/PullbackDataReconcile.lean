module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitPerfectEssSurjCanonicalPullbackData
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.ExtensionByZeroBaseChangeComparison

/-!
# Reconciling the two pullback-pseudofunctor data of derived pullback

`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` and
`AlgebraicGeometry.Space.canonicalPullbackData` are two `CategoryTheory.PullbackData` with the
same inverse images and different composition comparisons: the first takes the universal
comparison of the total left derived functor along a composite, the second the composition
comparison of Stacks 0D6D transported along the 2-isomorphism of Stacks 03G8.  Identifying them
is what lets the hom-level colimit statement of Stacks 09RI, proved for one of them, be read for
the other.

This file supplies the step of that identification which is pure category theory: **the
comparison of a presented factorisation of the derived datum is pinned by a degreewise
comparison**, for an arbitrary `CategoryTheory.PullbackData.LeftDerived`, over free variables.
The derived comparison is a left derived lift, so it is pinned by its composite with the
comparison `Lk^* ⟶ k^*` (`CategoryTheory.PullbackData.LeftDerived.triangle_inv_app_comp_α`); the
comparison of `AlgebraicGeometry.Space.DerivedPullbackComposition.canonical` satisfies the same
equation with the degreewise identification of the factorisation in place of
`CategoryTheory.PullbackData.triangle`
(`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp`).  So the two agree as
soon as those two degreewise identifications agree, and that is an equation between functors on
homotopy categories of complexes of `𝒪`-modules — no derived category and no localization in it.

## Main results

* `CategoryTheory.PullbackData.LeftDerived.triangle_inv_eq_of_degreewise` and
  `CategoryTheory.PullbackData.LeftDerived.triangle_eq_symm_of_degreewise`: **the comparison of
  a presented factorisation of the derived datum is the unique natural transformation whose
  composite with the comparison `Lk^* ⟶ k^*` is computed by a given degreewise comparison.**
  This is the uniqueness half of the universal property of the left derived functor along `k`,
  in the form a consumer with a candidate comparison in hand needs.
* `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived_L`,
  `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived_α`,
  `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived_Q` and
  `AlgebraicGeometry.Space.modulePullbackDataTopos_mapHomotopyCategory_pull`: the fields of
  `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` in the names in which
  `AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` is stated.  In
  particular the first says that the two data of the opening paragraph have the same inverse
  images.
* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp_α_rhs`: the
  right-hand side of that characterising equation, in the fields' spelling.

## What is reduced to what, and what is still open

The degreewise equation the generic result asks for is

```
(modulePullbackDataTopos B S hS).mapHomotopyCategory.triangle h =
  (smallEtalePullbackMapHomotopyFactorIso f g k h).symm
```

the equality of the two *degreewise* identifications of a factorisation `f ≫ g = k`: the one
built from the composition comparison of Stacks 03LU
(`AlgebraicGeometry.Space.modulePullbackCompIso`) and the one built from the composition
comparison of Stacks 03D6, part (2)
(`AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso`) followed by the action of the
2-isomorphism of Stacks 03G8
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_compTwoIso`).  Applying
`CategoryTheory.PullbackData.mapHomotopyCategory` degreewise to complexes is formal, so that
equation is equivalent to the underived statement

```
(modulePullbackDataTopos B S hS).compIso f g =
  (pullbackModulesCompTransport B S hS f g).symm ≪≫
    AlgebraicGeometry.RingedToposHom.pullbackModulesCompIso
      (smallEtaleRingedToposHom B S hS f) (smallEtaleRingedToposHom B S hS g)
```

whose two sides are isomorphisms of left adjoints of the *same* direct image — the direct-image
halves agree, `AlgebraicGeometry.Space.modulePushforwardCompIso` being by construction
`AlgebraicGeometry.RingedToposHom.pushforwardModulesCompIso` followed by
`AlgebraicGeometry.Space.pushforwardModulesCompTransport`, which
`AlgebraicGeometry.Space.pushforwardModulesCompTransport_eq_compTwoIso` identifies with the
action of the 2-isomorphism.  What is missing is the identification of the two adjunctions
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModules`, stated through the two-field
reading `AlgebraicGeometry.RingedToposHom.toModulesHom`, with
`AlgebraicGeometry.RingedToposHom.pullbackAdjPushforwardModulesViaComparison`, stated through the
four-field reading `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` over which
`AlgebraicGeometry.Space.modulePullbackAdjunction` is built.  The two readings are equal by
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom` but not
definitionally, and the library deliberately keeps the two adjunctions as separate declarations
rather than bridging them.  That bridge is the remaining content.

A second obstruction, of spelling rather than of mathematics, stops the generic result from being
instantiated here even with the degreewise equation in hand.
`AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` is stated where the preadditive
structure of the modules is `SheafOfModules.instPreadditive`, and
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` where it is the one
`SheafOfModules.instAbelian` induces.  The two are definitionally equal, and each field of the
former is identified with its name in the latter's spelling by one of the `rfl`s below.  But the
*left-hand side* of the characterising equation applies
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso` at an object written through the
localization functor, and crossing the two spellings underneath that application has to compare
`DerivedCategory.Qh` with itself at the two instances, through `HomologicalComplexUpToQuasiIso.Qh`
and `getLimitCone`, whose definitions are not exposed.  That `rfl` elaborates and is then rejected
by the kernel.  Aligning the preadditive spelling of the two files would remove it.

## Implementation notes

Each of the spelling bridges below is a `rfl` between a field of
`AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` and the name in which
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` is stated, and each is
a declaration of its own on purpose: stating the characterising equation directly in the fields'
spelling makes one declaration whose definitional unfoldings the kernel repeats, and that does
not terminate inside the heartbeat limit.  Separated, each unfolding is checked once.

The abelian structure of the modules is fixed to `SheafOfModules.instAbelian` and the preadditive
structure to the one it induces, as in the file that
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` lives in, so that the
statements here spell those instances the way `DerivedCategory.Qh` does.

## References

* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Lemma 75.24.2 (Tag 09RI)](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.PullbackData.LeftDerived

variable {A : Type u₁} [Category.{v₁} A] {K : A → Type u₂} [∀ a, Category.{v₂} (K a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)] {P : PullbackData A K} (E : P.LeftDerived D)

/-- **The comparison of a presented factorisation of the derived datum is pinned by a degreewise
comparison.**  If a natural transformation `β : Lg^* ⋙ Lf^* ⟶ Lk^*` composed with the comparison
`Lk^* ⟶ k^*` is computed, at every object in the image of the localization, by a degreewise
natural transformation `δ` equal to the comparison of the underived datum, then `β` *is* the
comparison of the derived datum.

Both sides are maps out of `Lg^* ⋙ Lf^*` into the left derived functor `Lk^*` of `k^* ⋙ Q`, so
`CategoryTheory.Functor.leftDerived_ext` reduces the identity to the stated equation, which
`CategoryTheory.PullbackData.LeftDerived.triangle_inv_app_comp_α` supplies for the comparison of
the derived datum. -/
theorem triangle_inv_eq_of_degreewise {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (β : E.L g ⋙ E.L f ⟶ E.L k) (δ : P.pull g ⋙ P.pull f ⟶ P.pull k)
    (hδ : δ = (P.triangle hk).inv)
    (hβ : ∀ M : K c, β.app ((E.Q c).obj M) ≫ (E.α k).app M =
      (E.L f).map ((E.α g).app M) ≫ (E.α f).app ((P.pull g).obj M) ≫
        (E.Q a).map (δ.app M)) :
    (E.toPullbackData.triangle hk).inv = β := by
  subst hδ
  refine (E.L k).leftDerived_ext (E.α k) (E.W c) (E.L g ⋙ E.L f) _ β ?_
  ext M
  rw [NatTrans.comp_app, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerLeft_app,
    E.triangle_inv_app_comp_α hk M, hβ M]

/-- `CategoryTheory.PullbackData.LeftDerived.triangle_inv_eq_of_degreewise` as an equation of
isomorphisms, which is the form that transports a statement written with one datum to the
other. -/
theorem triangle_eq_symm_of_degreewise {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) (Θ : E.L g ⋙ E.L f ≅ E.L k) (δ : P.pull g ⋙ P.pull f ≅ P.pull k)
    (hδ : δ = (P.triangle hk).symm)
    (hβ : ∀ M : K c, Θ.hom.app ((E.Q c).obj M) ≫ (E.α k).app M =
      (E.L f).map ((E.α g).app M) ≫ (E.α f).app ((P.pull g).obj M) ≫
        (E.Q a).map (δ.hom.app M)) :
    E.toPullbackData.triangle hk = Θ.symm :=
  Iso.ext ((Iso.inv_eq_inv (E.toPullbackData.triangle hk) Θ.symm).1
    (triangle_inv_eq_of_degreewise E hk Θ.hom δ.hom (congrArg Iso.hom hδ) hβ))

end CategoryTheory.PullbackData.LeftDerived

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] SheafOfModules.instAbelian
attribute [local instance 3000] Abelian.toPreadditive

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y Z : AlgebraicSpaces B S hS}

/-! ### The spelling bridges -/

/-- The derived inverse image of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` is
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullback`. -/
theorem derivedModulePullbackLeftDerived_L (f : X ⟶ Y) :
    (derivedModulePullbackLeftDerived B S hS).L f =
      smallEtaleDerivedModulePullback B S hS f :=
  rfl

/-- The comparison of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` is
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackComparison'`. -/
theorem derivedModulePullbackLeftDerived_α (f : X ⟶ Y) :
    (derivedModulePullbackLeftDerived B S hS).α f =
      smallEtaleDerivedModulePullbackComparison' (B := B) (S := S) (hS := hS) f :=
  rfl

/-- The localization functor of `AlgebraicGeometry.Space.derivedModulePullbackLeftDerived` is
`DerivedCategory.Qh`. -/
theorem derivedModulePullbackLeftDerived_Q (W : AlgebraicSpaces B S hS) :
    (derivedModulePullbackLeftDerived B S hS).Q W =
      DerivedCategory.Qh (C := SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W)) :=
  rfl

/-- The inverse image of the datum induced on homotopy categories is
`AlgebraicGeometry.Space.smallEtaleModulePullbackMapHomotopy`. -/
theorem modulePullbackDataTopos_mapHomotopyCategory_pull (f : X ⟶ Y) :
    (modulePullbackDataTopos B S hS).mapHomotopyCategory.pull f =
      smallEtaleModulePullbackMapHomotopy (B := B) (S := S) (hS := hS) f :=
  rfl

/-! ### The characterising equation in the fields' spelling -/

/-- The right-hand side of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackFactorIso_hom_app_comp` in the fields of
`AlgebraicGeometry.Space.derivedModulePullbackLeftDerived`. -/
theorem smallEtaleDerivedPullbackFactorIso_hom_app_comp_α_rhs (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (h : f ≫ g = k)
    (M : HomotopyCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
      (ComplexShape.up ℤ)) :
    ((derivedModulePullbackLeftDerived B S hS).L f).map
          (((derivedModulePullbackLeftDerived B S hS).α g).app M) ≫
        ((derivedModulePullbackLeftDerived B S hS).α f).app
          (((modulePullbackDataTopos B S hS).mapHomotopyCategory.pull g).obj M) ≫
        ((derivedModulePullbackLeftDerived B S hS).Q X).map
          ((smallEtalePullbackMapHomotopyFactorIso (B := B) (S := S) (hS := hS)
            f g k h).hom.app M) =
      (smallEtaleDerivedModulePullback B S hS f).map
          ((smallEtaleDerivedModulePullbackComparison' (B := B) (S := S) (hS := hS) g).app M) ≫
        (smallEtaleDerivedModulePullbackComparison' (B := B) (S := S) (hS := hS) f).app
          ((smallEtaleModulePullbackMapHomotopy (B := B) (S := S) (hS := hS) g).obj M) ≫
        DerivedCategory.Qh.map
          ((smallEtalePullbackMapHomotopyFactorIso (B := B) (S := S) (hS := hS)
            f g k h).hom.app M) :=
  rfl

end AlgebraicGeometry.Space

end
