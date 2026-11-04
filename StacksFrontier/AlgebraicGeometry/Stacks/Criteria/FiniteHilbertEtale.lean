module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.Functoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance

/-!
# The induced morphism of finite Hilbert stacks is étale (Stacks 05XS)

Let
```
  𝒳' --G--> 𝒳
   |         |
   F'        F
   v         v
  𝒴' --H--> 𝒴
```
be a 2-commutative diagram of stacks in groupoids over the big fppf site `(Sch/S)_fppf`, with
2-commutativity witnessed by a 2-isomorphism `γ : H ∘ F' ⟶ F ∘ G`, and let
`ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` be the canonical 1-morphism of degree-`d` finite Hilbert stacks of
Stacks 05XN. Stacks 05XS says that if `G` and `H` are representable by algebraic spaces and
étale, then so is `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)`; and that if moreover `H` is surjective and the
induced 1-morphism `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` is surjective, then `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` is surjective.

The proof is the source's. It factors the given square through `𝒳'' = 𝒳 ×_𝒴 𝒴'`, which splits
the canonical 1-morphism, up to 2-isomorphism, as
```
  ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳''/𝒴') ⟶ ℋ_d(𝒳/𝒴).
```
By Stacks 05XP the square
```
  ℋ_d(𝒳''/𝒴') --> ℋ_d(𝒳/𝒴)
       |                |
       v                v
       𝒴'      --H-->   𝒴
```
whose vertical arrows are the forgetful 1-morphisms of Stacks 05WD is 2-cartesian, so
`ℋ_d(𝒳''/𝒴') ⟶ ℋ_d(𝒳/𝒴)` is a base change of `H` and therefore inherits from it both
representability by algebraic spaces together with étaleness (Stacks 045C) and surjectivity
(Stacks 06D5). The first factor is the 1-morphism of Stacks 05XN of a square whose target column
is the identity of `𝒴'`, and whose top arrow `𝒳' ⟶ 𝒳''` is representable by algebraic spaces and
étale by Stacks 05XK; so Stacks 05YG applies to it. The two factors compose by Stacks 045B and
06D6.

## Main definitions

* `AlgebraicGeometry.Stack.stackFibered` and `AlgebraicGeometry.Stack.stackMapFibered`: a stack in
  groupoids and a 1-morphism of stacks in groupoids, read as a category fibred in groupoids and a
  1-morphism of such.
* `AlgebraicGeometry.Stack.finiteHilbertFibered`: the relative finite Hilbert stack `ℋ_d(𝒳/𝒴)`,
  read as a category fibred in groupoids.
* `AlgebraicGeometry.Stack.forgetTargetFibered` and `AlgebraicGeometry.Stack.mapRelativeFibered`:
  the forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ 𝒴` of Stacks 05WD and the canonical 1-morphism
  `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN, read as 1-morphisms of categories fibred in groupoids.
* `AlgebraicGeometry.Stack.targetFibreProduct`: the stack `𝒳'' = 𝒳 ×_𝒴 𝒴'`, with its projections
  `AlgebraicGeometry.Stack.targetFibreProductFst` and
  `AlgebraicGeometry.Stack.targetFibreProductSnd` and the comparison
  `AlgebraicGeometry.Stack.targetFibreProductComparison : 𝒳' ⟶ 𝒳''`.

## Main results

* `AlgebraicGeometry.Stack.isRelativelyEtale_mapRelativeFibered`: **Stacks 05XS, part (1)**.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_mapRelativeFibered`: **Stacks 05XS, part (2)**.
* `AlgebraicGeometry.Stack.mapRelativeFibered_factorizationIso`: the pasting law, identifying the
  canonical 1-morphism with the composite of the two factors.
* `AlgebraicGeometry.Stack.isRelativelyEtale_finiteHilbertBaseChange` and
  `AlgebraicGeometry.Stack.isSurjectiveOnObjects_finiteHilbertBaseChange`: the case of a
  2-cartesian given square, which is the second factor.

## Implementation notes

The induced 1-morphism `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` of the source is read as the comparison
`AlgebraicGeometry.Stack.targetFibreProductComparison` into the 2-fibre product over the site of
Stacks 0040, `𝒳 ×_𝒴 𝒴'`; that 2-fibre product is a stack in groupoids by
`CategoryTheory.TwoFibreProductOver.isStackInGroupoids_structureFunctor`, at the index universe of
the given stacks.

All four stacks are read at `CategoryTheory.CatFiberedInGroupoids.{u, u, u + 1, u + 1}`, the
universe assignment at which `AlgebraicGeometry.Stack.IsRelativelyEtale` is pinned. The relative
finite Hilbert category of stacks in groupoids whose underlying categories over the site are
`CategoryTheory.BasedCategory.{u, u + 1}` is again such a category over the site: an object is a
quintuple whose two site components and two stack components lie in `Type (u + 1)` and whose
identification lies in `Type u`, and a morphism has all four components in `Type u`.

`AlgebraicGeometry.Stack.IsRelativelyEtale` packages representability by algebraic spaces together
with the relative property of Stacks 03YK at étaleness, so it is exactly the source's
"representable by algebraic spaces and étale". Surjectivity is
`AlgebraicGeometry.Stack.IsSurjectiveOnObjects`, the notion of Stacks 06D4; it is converted to and
from the relative property of Stacks 03YK at surjectivity of morphisms of algebraic spaces by
Stacks 06D7, which is what makes the base change of Stacks 045C available for it at a square that
is an arbitrary 2-fibre product rather than the canonical one.

The two 1-morphisms of finite Hilbert stacks around the pasting are 2-isomorphic rather than
equal: their identifications differ by a composition with an identity.

## References

* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 05WD](https://stacks.math.columbia.edu/tag/05WD)
* [Stacks Project, Tag 05XK](https://stacks.math.columbia.edu/tag/05XK)
* [Stacks Project, Tag 05XN](https://stacks.math.columbia.edu/tag/05XN)
* [Stacks Project, Tag 05XP](https://stacks.math.columbia.edu/tag/05XP)
* [Stacks Project, Tag 05XS](https://stacks.math.columbia.edu/tag/05XS)
* [Stacks Project, Tag 05YG](https://stacks.math.columbia.edu/tag/05YG)
* [Stacks Project, Tag 06D4](https://stacks.math.columbia.edu/tag/06D4)
* [Stacks Project, Tag 06D5](https://stacks.math.columbia.edu/tag/06D5)
* [Stacks Project, Tag 06D6](https://stacks.math.columbia.edu/tag/06D6)
* [Stacks Project, Tag 06D7](https://stacks.math.columbia.edu/tag/06D7)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (d : ℕ)

/-- A stack in groupoids over the big fppf site of `S`, regarded as a category fibred in
groupoids over that site: a stack in groupoids is in particular fibred in groupoids. -/
def stackFibered (𝒵 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS)) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk 𝒵.toBasedCategory 𝒵.isStackInGroupoids.isFiberedInGroupoids

/-- A 1-morphism of stacks in groupoids, regarded as a 1-morphism of the associated categories
fibred in groupoids. -/
def stackMapFibered {𝒵 𝒲 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS)}
    (K : 𝒵.toBasedCategory ⥤ᵇ 𝒲.toBasedCategory) :
    stackFibered B S hS 𝒵 ⟶ stackFibered B S hS 𝒲 :=
  Bicategory.InducedBicategory.mkHom K

variable (𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS))
  (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)

/-- The relative degree-`d` finite Hilbert stack `ℋ_d(𝒳/𝒴)` of a 1-morphism `F : 𝒳 ⟶ 𝒴` of
stacks in groupoids, regarded as a category fibred in groupoids over the big fppf site of `S`. -/
noncomputable def finiteHilbertFibered :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
    (isFiberedInGroupoids_finiteHilbertProjection (B := B) (S := S) (hS := hS) (𝒳 := 𝒳)
      (𝒴 := 𝒴) (F := F) (d := d))

/-- **Stacks 05WD.** The forgetful 1-morphism `ℋ_d(𝒳/𝒴) ⟶ 𝒴` to the target stack, regarded as a
1-morphism of categories fibred in groupoids over the big fppf site of `S`. -/
noncomputable def forgetTargetFibered :
    finiteHilbertFibered B S hS d 𝒳 𝒴 F ⟶ stackFibered B S hS 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (forgetTarget (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))

variable (𝒳' 𝒴' : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS))
  (F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴'.toBasedCategory)
  (G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory)
  (H : 𝒴'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)

/-- **Stacks 05XN.** The canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` attached to a
2-commutative square of stacks in groupoids, regarded as a 1-morphism of categories fibred in
groupoids over the big fppf site of `S`. -/
noncomputable def mapRelativeFibered
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F) :
    finiteHilbertFibered B S hS d 𝒳' 𝒴' F' ⟶ finiteHilbertFibered B S hS d 𝒳 𝒴 F :=
  Bicategory.InducedBicategory.mkHom (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)

/-- **The case of a 2-cartesian square of Stacks 05XS, at étaleness.** Let `H : 𝒴' ⟶ 𝒴` be a
1-morphism of stacks in groupoids over the big fppf site of `S` which is representable by algebraic
spaces and étale, and let the given 2-commutative square with horizontal arrows `G`, `H`, vertical
arrows `F'`, `F` and filler `γ` be 2-cartesian, so that `𝒳'` is the 2-fibre product `𝒴' ×_𝒴 𝒳`.
Then the canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN is representable by algebraic
spaces and étale.

By Stacks 05XP (`AlgebraicGeometry.Stack.isTwoFibreProduct_hilbertSquare`) the induced square of
finite Hilbert stacks is 2-cartesian, so the 1-morphism is a base change of `H` along the forgetful
1-morphism `ℋ_d(𝒳/𝒴) ⟶ 𝒴` of Stacks 05WD; Stacks 045C, the base change of the relative property of
Stacks 03YK, at étaleness then gives the conclusion. This is the right-hand factor of the
factorization by which Stacks 05XS is proved. -/
theorem isRelativelyEtale_finiteHilbertBaseChange
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hcart : Bicategory.IsTwoFibreProduct
      (sourceSquare.{u, w, u, u} B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ))
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H)) :
    IsRelativelyEtale B S hS (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) :=
  isRelativelyEtale_baseChange B S hS (stackFibered B S hS 𝒴') (stackFibered B S hS 𝒴)
    (finiteHilbertFibered B S hS d 𝒳 𝒴 F) (stackMapFibered B S hS H)
    (forgetTargetFibered B S hS d 𝒳 𝒴 F)
    (hilbertSquare.{u, w, u, u} B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ)
    (isTwoFibreProduct_hilbertSquare.{u, w, u, u} B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ hcart) hH

/-- **The case of a 2-cartesian square of Stacks 05XS, at surjectivity.** Let `H : 𝒴' ⟶ 𝒴` be a
1-morphism of stacks in groupoids over the big fppf site of `S` which is representable by algebraic
spaces, étale and surjective, and let the given 2-commutative square be 2-cartesian, so that `𝒳'`
is the 2-fibre product `𝒴' ×_𝒴 𝒳`. Then the canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks
05XN is surjective.

By Stacks 05XP the induced square of finite Hilbert stacks is 2-cartesian, so the 1-morphism is a
base change of `H`. Surjectivity on objects is the relative property of Stacks 03YK at surjectivity
of morphisms of algebraic spaces by Stacks 06D7, and that property is inherited by base changes by
Stacks 045C; together they are Stacks 06D5. -/
theorem isSurjectiveOnObjects_finiteHilbertBaseChange
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hcart : Bicategory.IsTwoFibreProduct
      (sourceSquare.{u, w, u, u} B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ))
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H))
    (hHSurj : IsSurjectiveOnObjects B S hS (stackFibered B S hS 𝒴').val.p
      (stackFibered B S hS 𝒴).val.p
      (CatFiberedInGroupoids.homFunctor (stackMapFibered B S hS H))) :
    IsSurjectiveOnObjects B S hS (finiteHilbertFibered B S hS d 𝒳' 𝒴' F').val.p
      (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p
      (CatFiberedInGroupoids.homFunctor
        (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)) := by
  have hR := isTwoFibreProduct_hilbertSquare.{u, w, u, u} B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ hcart
  have hFstRep := (isRelativelyEtale_finiteHilbertBaseChange B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ
    hcart hH).1
  have hFstSurj := hasRelativeProperty_baseChange.{u, u, u + 1, u} B S hS
    (Space.surjectiveMorphismProperty B S hS)
    (stackFibered B S hS 𝒴') (stackFibered B S hS 𝒴)
    (finiteHilbertFibered B S hS d 𝒳 𝒴 F) (stackMapFibered B S hS H)
    (forgetTargetFibered B S hS d 𝒳 𝒴 F)
    (hilbertSquare.{u, w, u, u} B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ) hR hH.1
    ((isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
      (stackMapFibered B S hS H) hH.1).1 hHSurj)
  exact (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, u, u + 1, u} B S hS
    (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) hFstRep).2 hFstSurj

/-! ### The factorization through `𝒳 ×_𝒴 𝒴'` -/

/-- The 2-fibre product `𝒳 ×_𝒴 𝒴'` of `F : 𝒳 ⟶ 𝒴` and `H : 𝒴' ⟶ 𝒴`, the stack `𝒳''` through
which the proof of Stacks 05XS factors the given square. It is the 2-fibre product over the site
of Stacks 0040, which is a stack in groupoids by
`CategoryTheory.TwoFibreProductOver.isStackInGroupoids_structureFunctor`. -/
noncomputable def targetFibreProduct
    (𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS))
    (F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory)
    (𝒴' : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS))
    (H : 𝒴'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory) :
    StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
      (BigFppfOver.topology B S hS) where
  toBasedCategory := BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor
    𝒳.toBasedCategory.p 𝒴'.toBasedCategory.p 𝒴.toBasedCategory.p F.toFunctor H.toFunctor)
  isStackInGroupoids := TwoFibreProductOver.isStackInGroupoids_structureFunctor _ _ _ _ _ F.w H.w
    _ 𝒳.isStackInGroupoids 𝒴'.isStackInGroupoids 𝒴.isStackInGroupoids

/-- The first projection `𝒳 ×_𝒴 𝒴' ⟶ 𝒳`. -/
def targetFibreProductFst :
    (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H).toBasedCategory ⥤ᵇ 𝒳.toBasedCategory where
  toFunctor := TwoFibreProductOver.fst _ _ _ _ _
  w := TwoFibreProductOver.fst_comp_eq

/-- The second projection `𝒳 ×_𝒴 𝒴' ⟶ 𝒴'`. -/
def targetFibreProductSnd :
    (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H).toBasedCategory ⥤ᵇ 𝒴'.toBasedCategory where
  toFunctor := TwoFibreProductOver.snd _ _ _ _ _
  w := TwoFibreProductOver.snd_comp_eq

/-- The 2-isomorphism `H ∘ pr₂ ⟶ F ∘ pr₁` filling the square of the 2-fibre product
`𝒳 ×_𝒴 𝒴'`: its component at `(U, x, y', φ)` is the inverse of the comparison isomorphism
`φ : F x ≅ H y'`. -/
noncomputable def targetFibreProductIso :
    BasedFunctor.comp (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) H ≅
      BasedFunctor.comp (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H) F :=
  (BasedNatIso.mkNatIso (TwoFibreProductOver.psiIso _ _ _ _ _)
    (fun x => TwoFibreProductOver.psiIso_hom_vertical x)).symm

/-- The comparison 1-morphism `𝒳' ⟶ 𝒳 ×_𝒴 𝒴'` induced by the given 2-commutative square. -/
def targetFibreProductComparison (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F) :
    𝒳'.toBasedCategory ⥤ᵇ (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H).toBasedCategory where
  toFunctor := sourceComparison.{u, w, u, u} B S hS 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ
  w := TwoFibreProductOver.lift_comp_structureFunctor _ _ _ _ _ _ _ _ _ _ _ _

/-- The left-hand square of the factorization commutes on the nose: the second projection of the
comparison `𝒳' ⟶ 𝒳 ×_𝒴 𝒴'` is `F'`. -/
def targetFibreProductComparisonIso (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F) :
    BasedFunctor.comp F' (𝟙 𝒴'.toBasedCategory) ≅
      BasedFunctor.comp (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)
        (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) :=
  Iso.refl _

/-- The square of the 2-fibre product `𝒳 ×_𝒴 𝒴'` is 2-cartesian: as a square of categories fibred
in groupoids it is the canonical 2-fibre product square of the cospan `(F, H)`. -/
noncomputable def isTwoFibreProduct_targetFibreProductSquare :
    Bicategory.IsTwoFibreProduct
      (sourceSquare.{u, w, u, u} B S hS (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴' 𝒳 𝒴
        (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) F (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H) H
        (targetFibreProductIso B S hS 𝒳 𝒴 F 𝒴' H)) :=
  CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
    (Bicategory.InducedBicategory.mkHom (X := toCatFiberedInGroupoids.{u, w, u, u} B S hS 𝒳)
      (Y := toCatFiberedInGroupoids.{u, w, u, u} B S hS 𝒴) F)
    (Bicategory.InducedBicategory.mkHom (X := toCatFiberedInGroupoids.{u, w, u, u} B S hS 𝒴')
      (Y := toCatFiberedInGroupoids.{u, w, u, u} B S hS 𝒴) H)

/-- The component at an object `P` of `ℋ_d(𝒳'/𝒴')` of the pasting isomorphism: the image of `P`
under the canonical 1-morphism of the given square and its image under the composite of the
canonical 1-morphisms of the two squares of the factorization differ only by an identity in
their identifications, so all four components of the comparison are identities. -/
@[simps]
def factorizationIsoApp (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (P : FiniteHilbert.Object B S hS 𝒳' 𝒴' F' d) :
    (mapRelative B S hS d 𝒳' 𝒴' 𝒳 𝒴 F' F G H γ).obj P ≅
      (mapRelative B S hS d (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴' 𝒳 𝒴
          (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) F
          (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H) H
          (targetFibreProductIso B S hS 𝒳 𝒴 F 𝒴' H)).obj
        ((mapRelative B S hS d 𝒳' 𝒴' (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴' F'
          (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H)
          (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) (𝟙 𝒴'.toBasedCategory)
          (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)).obj P) where
  hom :=
    { f := 𝟙 P.U
      g := 𝟙 P.Z
      square := IsPullback.id_horiz P.q
      b := 𝟙 (H.obj P.y)
      b_over := IsHomLift.id ((H.w_obj P.y).trans P.y_over)
      a := 𝟙 (G.obj P.x)
      a_over := IsHomLift.id ((G.w_obj P.x).trans P.x_over)
      compatible := by
        change F.map (𝟙 _) ≫ (squareComparison γ P.x ≫ H.map (𝟙 _ ≫ P.α)) =
          (squareComparison γ P.x ≫ H.map P.α) ≫ 𝟙 _
        simp }
  inv :=
    { f := 𝟙 P.U
      g := 𝟙 P.Z
      square := IsPullback.id_horiz P.q
      b := 𝟙 (H.obj P.y)
      b_over := IsHomLift.id ((H.w_obj P.y).trans P.y_over)
      a := 𝟙 (G.obj P.x)
      a_over := IsHomLift.id ((G.w_obj P.x).trans P.x_over)
      compatible := by
        change F.map (𝟙 _) ≫ (squareComparison γ P.x ≫ H.map P.α) =
          (squareComparison γ P.x ≫ H.map (𝟙 _ ≫ P.α)) ≫ 𝟙 _
        simp }
  hom_inv_id := FiniteHilbert.Hom.ext (Category.comp_id _) (Category.comp_id _)
    (Category.comp_id _) (Category.comp_id _)
  inv_hom_id := FiniteHilbert.Hom.ext (Category.comp_id _) (Category.comp_id _)
    (Category.comp_id _) (Category.comp_id _)

/-- **The pasting law for the factorization of Stacks 05XS.** The canonical 1-morphism
`ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN attached to the given square is 2-isomorphic to the
composite of the canonical 1-morphisms
`ℋ_d(𝒳'/𝒴') ⟶ ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴') ⟶ ℋ_d(𝒳/𝒴)` attached to the two squares into which the given
square factors through the 2-fibre product `𝒳 ×_𝒴 𝒴'`. -/
noncomputable def mapRelativeFibered_factorizationIso
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F) :
    mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ ≅
      mapRelativeFibered B S hS d (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴'
          (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) 𝒳' 𝒴' F'
          (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) (𝟙 𝒴'.toBasedCategory)
          (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) ≫
        mapRelativeFibered B S hS d 𝒳 𝒴 F (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴'
          (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H)
          (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H) H
          (targetFibreProductIso B S hS 𝒳 𝒴 F 𝒴' H) :=
  Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (NatIso.ofComponents (factorizationIsoApp B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) (fun _φ =>
      FiniteHilbert.Hom.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
    (fun P => IsHomLift.map finiteHilbertProjection
      (factorizationIsoApp B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ P).hom))

/-- **The comparison `𝒳' ⟶ 𝒳 ×_𝒴 𝒴'` is representable by algebraic spaces and étale** as soon
as `G` and `H` are. Its composite with the first projection is `G`, and the first projection is a
base change of `H`, hence representable by algebraic spaces and étale by Stacks 045C; Stacks 05XK
then cancels it. This is the first step of the proof of Stacks 05XS. -/
theorem isRelativelyEtale_targetFibreProductComparison
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hG : IsRelativelyEtale B S hS (stackMapFibered B S hS G))
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H)) :
    IsRelativelyEtale B S hS
      (stackMapFibered B S hS (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)) :=
  isRelativelyEtale_of_comp B S hS _
    (stackMapFibered B S hS (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H)) hG
    (isRelativelyEtale_baseChange B S hS (stackFibered B S hS 𝒴') (stackFibered B S hS 𝒴)
      (stackFibered B S hS 𝒳) (stackMapFibered B S hS H) (stackMapFibered B S hS F)
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        (stackMapFibered B S hS F) (stackMapFibered B S hS H))
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (stackMapFibered B S hS F) (stackMapFibered B S hS H)) hH)

/-- **The reduction of Stacks 05XS to the case `𝒴' = 𝒴`, at étaleness.** If `H` is representable
by algebraic spaces and étale, then `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` is representable by algebraic spaces
and étale as soon as `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴')` is.

The 1-morphism is 2-isomorphic to the composite of that one with
`ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴') ⟶ ℋ_d(𝒳/𝒴)` (`AlgebraicGeometry.Stack.mapRelativeFibered_factorizationIso`),
which is a base change of `H` by Stacks 05XP and therefore representable by algebraic spaces and
étale by Stacks 045C (`AlgebraicGeometry.Stack.isRelativelyEtale_finiteHilbertBaseChange`); the
composite is then representable by algebraic spaces and étale by Stacks 045B. -/
theorem isRelativelyEtale_mapRelativeFibered_of_comparison
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H))
    (hL : IsRelativelyEtale B S hS
      (mapRelativeFibered B S hS d (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴'
        (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) 𝒳' 𝒴' F'
        (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) (𝟙 𝒴'.toBasedCategory)
        (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ))) :
    IsRelativelyEtale B S hS (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) :=
  isRelativelyEtale_congr_twoIso B S hS
    (mapRelativeFibered_factorizationIso B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ).symm
    (isRelativelyEtale_comp B S hS _ _ hL
      (isRelativelyEtale_finiteHilbertBaseChange B S hS d 𝒳 𝒴 F
        (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴' (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H)
        (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H) H (targetFibreProductIso B S hS 𝒳 𝒴 F 𝒴' H)
        (isTwoFibreProduct_targetFibreProductSquare B S hS 𝒳 𝒴 F 𝒴' H) hH))

/-- **The reduction of Stacks 05XS to the case `𝒴' = 𝒴`, at surjectivity.** If `H` is
representable by algebraic spaces, étale and surjective, then `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` is
surjective as soon as `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴')` is.

The second factor of the factorization is surjective by
`AlgebraicGeometry.Stack.isSurjectiveOnObjects_finiteHilbertBaseChange`, the composite by
Stacks 06D6, and surjectivity on objects passes along the vertical 2-isomorphism
`AlgebraicGeometry.Stack.mapRelativeFibered_factorizationIso`. -/
theorem isSurjectiveOnObjects_mapRelativeFibered_of_comparison
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H))
    (hHSurj : IsSurjectiveOnObjects B S hS (stackFibered B S hS 𝒴').val.p
      (stackFibered B S hS 𝒴).val.p
      (CatFiberedInGroupoids.homFunctor (stackMapFibered B S hS H)))
    (hL : IsSurjectiveOnObjects B S hS (finiteHilbertFibered B S hS d 𝒳' 𝒴' F').val.p
      (finiteHilbertFibered B S hS d (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴'
        (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H)).val.p
      (CatFiberedInGroupoids.homFunctor
        (mapRelativeFibered B S hS d (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴'
          (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H) 𝒳' 𝒴' F'
          (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) (𝟙 𝒴'.toBasedCategory)
          (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)))) :
    IsSurjectiveOnObjects B S hS (finiteHilbertFibered B S hS d 𝒳' 𝒴' F').val.p
      (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p
      (CatFiberedInGroupoids.homFunctor
        (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)) := by
  have hR := isSurjectiveOnObjects_finiteHilbertBaseChange B S hS d 𝒳 𝒴 F
    (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H) 𝒴' (targetFibreProductSnd B S hS 𝒳 𝒴 F 𝒴' H)
    (targetFibreProductFst B S hS 𝒳 𝒴 F 𝒴' H) H (targetFibreProductIso B S hS 𝒳 𝒴 F 𝒴' H)
    (isTwoFibreProduct_targetFibreProductSquare B S hS 𝒳 𝒴 F 𝒴' H) hH hHSurj
  have hcomp := isSurjectiveOnObjects_comp B S hS _ _ _ _ _
    (CatFiberedInGroupoids.homFunctor_comp_p _) hL hR
  intro U hU z hz
  obtain ⟨V, hV, f, x, hx, α, hα⟩ := hcomp U hU z hz
  let e := factorizationIsoApp B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ x
  refine ⟨V, hV, f, x, hx, e.hom ≫ α, ?_⟩
  have he : (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p.IsHomLift (𝟙 V) e.hom := by
    subst hx
    exact IsHomLift.map finiteHilbertProjection e.hom
  have h := @IsHomLift.comp _ _ _ _ (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p _ _ _ _ _ _
    (𝟙 V) f e.hom α he hα
  rwa [Category.id_comp] at h

/-- **Stacks 05XS, part (1).** Let `G : 𝒳' ⟶ 𝒳` and `H : 𝒴' ⟶ 𝒴` be 1-morphisms of stacks in
groupoids over the big fppf site of `S` which are representable by algebraic spaces and étale,
and let `γ : H ∘ F' ⟶ F ∘ G` make the square with vertical arrows `F'`, `F` 2-commute. Then the
canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN is representable by algebraic
spaces and étale.

The proof is the source's. The 1-morphism is 2-isomorphic to the composite of
`ℋ_d(𝒳'/𝒴') ⟶ ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴')`, which is representable by algebraic spaces and étale by
Stacks 05YG because `𝒳' ⟶ 𝒳 ×_𝒴 𝒴'` is by Stacks 05XK, with
`ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴') ⟶ ℋ_d(𝒳/𝒴)`, which is a base change of `H` by Stacks 05XP and therefore
representable by algebraic spaces and étale by Stacks 045C. -/
@[stacks 05XS "part (1)"]
theorem isRelativelyEtale_mapRelativeFibered
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hG : IsRelativelyEtale B S hS (stackMapFibered B S hS G))
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H)) :
    IsRelativelyEtale B S hS (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) := by
  obtain ⟨hLrep, hLet⟩ :=
    isRelativelyEtale_targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ hG hH
  exact isRelativelyEtale_mapRelativeFibered_of_comparison B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ hH
    ⟨isRepresentableByAlgebraicSpaces_mapRelative
        (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) hLrep hLet,
      isEtale_mapRelative (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)
        hLrep hLet⟩

/-- **Stacks 05XS, part (2).** Let `G : 𝒳' ⟶ 𝒳` and `H : 𝒴' ⟶ 𝒴` be 1-morphisms of stacks in
groupoids over the big fppf site of `S` which are representable by algebraic spaces and étale,
and let `γ : H ∘ F' ⟶ F ∘ G` make the square with vertical arrows `F'`, `F` 2-commute. If
moreover `H` is surjective and the induced 1-morphism `𝒳' ⟶ 𝒳 ×_𝒴 𝒴'` to the 2-fibre product is
surjective, then the canonical 1-morphism `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN is surjective.

The induced 1-morphism is `AlgebraicGeometry.Stack.targetFibreProductComparison`, into the
2-fibre product over the site of Stacks 0040, which the source writes `𝒴' ×_𝒴 𝒳`. The proof is
the source's: `ℋ_d(𝒳'/𝒴') ⟶ ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴')` is surjective by Stacks 05YG, the base change
`ℋ_d((𝒳 ×_𝒴 𝒴')/𝒴') ⟶ ℋ_d(𝒳/𝒴)` of `H` is surjective as `H` is, and composites of surjective
1-morphisms are surjective. -/
@[stacks 05XS "part (2)"]
theorem isSurjectiveOnObjects_mapRelativeFibered
    (γ : BasedFunctor.comp F' H ≅ BasedFunctor.comp G F)
    (hG : IsRelativelyEtale B S hS (stackMapFibered B S hS G))
    (hH : IsRelativelyEtale B S hS (stackMapFibered B S hS H))
    (hHSurj : IsSurjectiveOnObjects B S hS (stackFibered B S hS 𝒴').val.p
      (stackFibered B S hS 𝒴).val.p
      (CatFiberedInGroupoids.homFunctor (stackMapFibered B S hS H)))
    (hcomparison : IsSurjectiveOnObjects B S hS (stackFibered B S hS 𝒳').val.p
      (stackFibered B S hS (targetFibreProduct B S hS 𝒳 𝒴 F 𝒴' H)).val.p
      (CatFiberedInGroupoids.homFunctor (stackMapFibered B S hS
        (targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)))) :
    IsSurjectiveOnObjects B S hS (finiteHilbertFibered B S hS d 𝒳' 𝒴' F').val.p
      (finiteHilbertFibered B S hS d 𝒳 𝒴 F).val.p
      (CatFiberedInGroupoids.homFunctor
        (mapRelativeFibered B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ)) := by
  obtain ⟨hLrep, hLet⟩ :=
    isRelativelyEtale_targetFibreProductComparison B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ hG hH
  exact isSurjectiveOnObjects_mapRelativeFibered_of_comparison B S hS d 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ hH
    hHSurj (isSurjectiveOnObjects_mapRelative
      (targetFibreProductComparisonIso B S hS 𝒳 𝒴 F 𝒳' 𝒴' F' G H γ) hLrep hLet hcomparison)

end AlgebraicGeometry.Stack

end
