module

public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyCancelSourceLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Etale
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChangeRepresentableBySpace
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalSchemePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtale
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDeligneMumford
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableFromAlgebraicSpaces
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Pasting
public import StacksFrontier.CategoryTheory.TwoFibreProduct.Swap
public import StacksFrontier.CategoryTheory.TwoFibreProduct.StrictTwoCommSq
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Precomposing a relative diagonal with an étale 1-morphism

Let `k : 𝒲 ⟶ 𝒰` and `f : 𝒰 ⟶ 𝒱` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S`, with `k` relatively étale. The square

```
  𝒲  --Δ_{k ≫ f}-->  𝒲 ×_𝒱 𝒲
  |                      |
  k                    k × k
  v                      v
  𝒰  ----Δ_f------->  𝒰 ×_𝒱 𝒰
```

2-commutes, and `k × k` is a composite of two base changes of `k`, hence relatively étale. So
`k ≫ Δ_f` is relatively étale exactly when `Δ_{k ≫ f}` is. With `k` moreover surjective, étaleness
of `Δ_f` descends along `k`. For a 1-morphism between algebraic spaces read as categories, the
relative diagonal is étale exactly when the diagonal of the induced morphism of algebraic spaces
is.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.precompFst`, `CategoryTheory.TwoFibreProductOver.precompSnd`:
  applying a 1-morphism to one factor of a 2-fibre product over a base, keeping the comparison
  isomorphism.
* `AlgebraicGeometry.Stack.diagPrecompFst`, `AlgebraicGeometry.Stack.diagPrecompSnd`: the two
  factors of `k × k`.

## Main results

* `AlgebraicGeometry.Stack.isTwoFibreProduct_of_isTwoFibreProduct_paste_cat`: the converse of the
  pasting law for categories fibred in groupoids.
* `AlgebraicGeometry.Stack.isRelativelyEtale_diagPrecomp`: `k × k` is relatively étale.
* `AlgebraicGeometry.Stack.isRelativelyEtale_comp_relativeDiagonal_iff`: `k ≫ Δ_f` is relatively
  étale iff `Δ_{k ≫ f}` is.
* `AlgebraicGeometry.Stack.isRelativelyEtale_relativeDiagonal_iff_isEtale_diagonal`: for a
  1-morphism between algebraic spaces read as categories, its relative diagonal is relatively
  étale iff the diagonal of the induced morphism of algebraic spaces is étale.
* `AlgebraicGeometry.Stack.isRelativelyEtale_relativeDiagonal_of_comp`: étaleness of `Δ_f`
  descends along a surjective étale `k`.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 06M2](https://stacks.math.columbia.edu/tag/06M2)
* [Stacks Project, Tag 0CJ0](https://stacks.math.columbia.edu/tag/0CJ0)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe vC v₁ v₂ v₃ v₄ uC u₁ u₂ u₃ u₄

variable {𝒞 : Type uC} [Category.{vC} 𝒞]
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒳' : Type u₂} [Category.{v₂} 𝒳']
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞}

/-- Applying `k : 𝒳 ⥤ 𝒳'` to the first factor of `𝒳 ×_{k ⋙ F, 𝒮, G} 𝒴`: the object
`(U, x, y, φ)` goes to `(U, k x, y, φ)`, the comparison isomorphism being kept as it is. -/
def precompFst (k : 𝒳 ⥤ 𝒳') (hk : k ⋙ p𝒳' = p𝒳) (F : 𝒳' ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 (k ⋙ F) G ⥤ TwoFibreProductOver p𝒳' p𝒴 p𝒮 F G where
  obj P :=
    { base := P.base
      x := k.obj P.x
      y := P.y
      hx := (Functor.congr_obj hk P.x).trans P.hx
      hy := P.hy
      iso := P.iso
      vertical := P.vertical }
  map φ :=
    { hbase := φ.hbase
      a := k.map φ.a
      b := φ.b
      ha :=
        have := φ.ha
        Functor.isHomLift_map_of_comp_eq hk φ.hbase φ.a
      hb := φ.hb
      w := φ.w }
  map_id P := Hom.ext' (k.map_id P.x) rfl
  map_comp φ ψ := Hom.ext' (k.map_comp φ.a ψ.a) rfl

/-- Applying `k : 𝒳 ⥤ 𝒳'` to the second factor of `𝒴 ×_{G, 𝒮, k ⋙ F} 𝒳`: the object
`(U, y, x, φ)` goes to `(U, y, k x, φ)`. -/
def precompSnd (k : 𝒳 ⥤ 𝒳') (hk : k ⋙ p𝒳' = p𝒳) (G : 𝒴 ⥤ 𝒮) (F : 𝒳' ⥤ 𝒮) :
    TwoFibreProductOver p𝒴 p𝒳 p𝒮 G (k ⋙ F) ⥤ TwoFibreProductOver p𝒴 p𝒳' p𝒮 G F where
  obj P :=
    { base := P.base
      x := P.x
      y := k.obj P.y
      hx := P.hx
      hy := (Functor.congr_obj hk P.y).trans P.hy
      iso := P.iso
      vertical := P.vertical }
  map φ :=
    { hbase := φ.hbase
      a := φ.a
      b := k.map φ.b
      ha := φ.ha
      hb :=
        have := φ.hb
        Functor.isHomLift_map_of_comp_eq hk φ.hbase φ.b
      w := φ.w }
  map_id P := Hom.ext' rfl (k.map_id P.y)
  map_comp φ ψ := Hom.ext' rfl (k.map_comp φ.b ψ.b)

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {𝒲 𝒰 𝒱 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  (k : 𝒲 ⟶ 𝒰) (f : 𝒰 ⟶ 𝒱)

/-- `𝒲 ×_𝒱 𝒲 ⟶ 𝒰 ×_𝒱 𝒲`, applying `k` to the first factor. -/
def diagPrecompFst :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (k ≫ f) (k ≫ f)).pt ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f)).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.precompFst k.hom.toFunctor k.hom.w f.hom.toFunctor
        (k ≫ f).hom.toFunctor
      w := rfl }

/-- `𝒰 ×_𝒱 𝒲 ⟶ 𝒰 ×_𝒱 𝒰`, applying `k` to the second factor. -/
def diagPrecompSnd :
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f)).pt ⟶
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f).pt :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.precompSnd k.hom.toFunctor k.hom.w f.hom.toFunctor
        f.hom.toFunctor
      w := rfl }

/-- If `i`, `j` and `l` are identities, then `g ≫ i = j ≫ g ≫ l ≫ 𝟙 b`. -/
theorem comp_eq_of_maps_id {A : Type*} [Category A] {a b : A} (g : a ⟶ b) (i : b ⟶ b)
    (j : a ⟶ a) (l : b ⟶ b) (hi : i = 𝟙 b) (hj : j = 𝟙 a) (hl : l = 𝟙 b) :
    g ≫ i = j ≫ g ≫ l ≫ 𝟙 b := by
  subst hi hj hl
  simp

/-- The converse of the pasting law for categories fibred in groupoids: if `Q` and the pasted
rectangle `Q.paste T` are 2-fibre products, so is `T`. -/
noncomputable def isTwoFibreProduct_of_isTwoFibreProduct_paste_cat
    {𝒳 𝒴 𝒵 𝒯 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {f : 𝒳 ⟶ 𝒵} {g : 𝒴 ⟶ 𝒵} {k : 𝒯 ⟶ 𝒴}
    {Q : Bicategory.TwoCommSq f g} (hQ : Bicategory.IsTwoFibreProduct Q)
    (T : Bicategory.TwoCommSq Q.snd k) (hQT : Bicategory.IsTwoFibreProduct (Q.paste T)) :
    Bicategory.IsTwoFibreProduct T := by
  let C := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd k
  have hC : Bicategory.IsTwoFibreProduct C :=
    CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} Q.snd k
  let ρ : Bicategory.TwoCommSq.PreHom T C := Quotient.out (hC.from T)
  exact Bicategory.isTwoFibreProduct_of_isEquivalence_to hC ρ
    (Bicategory.isEquivalence_of_isTwoFibreProduct hQT (Bicategory.isTwoFibreProduct_paste hQ hC)
      (Bicategory.TwoCommSq.PreHom.paste Q ρ))

/-- The square exhibiting `diagPrecompFst` as a base change of `k`. -/
def diagPrecompFstSquare :
    Bicategory.TwoCommSq
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f)).fst k where
  pt := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (k ≫ f) (k ≫ f)).pt
  fst := diagPrecompFst B S hS k f
  snd := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (k ≫ f) (k ≫ f)).fst
  iso := Iso.refl _

/-- The square exhibiting `diagPrecompSnd` as a base change of `k`. -/
def diagPrecompSndSquare :
    Bicategory.TwoCommSq
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f).snd k where
  pt := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f)).pt
  fst := diagPrecompSnd B S hS k f
  snd := (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f)).snd
  iso := Iso.refl _

/-- Comparison of the swapped canonical square of `(k ≫ f, k ≫ f)` with the pasted rectangle. -/
def diagPrecompFstPasteHom :
    Bicategory.TwoCommSq.PreHom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} (k ≫ f) (k ≫ f)).swap
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f)).swap.paste
        (diagPrecompFstSquare B S hS k f)) :=
  CatFiberedInGroupoids.preHomOfStrict.{u, u, u + 1, u + 1} (𝟙 _) (Iso.refl _) (Iso.refl _) (by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext x
    change x.iso.inv ≫ (k ≫ f).hom.toFunctor.map (𝟙 _) =
      (k ≫ f).hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫ x.iso.inv ≫ 𝟙 _ ≫ f.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _
    simp only [Category.id_comp]
    exact comp_eq_of_maps_id _ _ _ _ ((k ≫ f).hom.toFunctor.map_id _)
      ((k ≫ f).hom.toFunctor.map_id _) (f.hom.toFunctor.map_id _))

/-- Comparison of the canonical square of `(f, k ≫ f)` with the pasted rectangle. -/
def diagPrecompSndPasteHom :
    Bicategory.TwoCommSq.PreHom
      (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f (k ≫ f))
      ((CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} f f).paste
        (diagPrecompSndSquare B S hS k f)) :=
  CatFiberedInGroupoids.preHomOfStrict.{u, u, u + 1, u + 1} (𝟙 _) (Iso.refl _) (Iso.refl _) (by
    apply Bicategory.InducedBicategory.hom₂_ext
    apply BasedNatTrans.ext
    ext x
    change x.iso.hom ≫ (k ≫ f).hom.toFunctor.map (𝟙 _) =
      f.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ ≫ x.iso.hom ≫ 𝟙 _ ≫ f.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _
    simp only [Category.id_comp]
    exact comp_eq_of_maps_id _ _ _ _ ((k ≫ f).hom.toFunctor.map_id _)
      (f.hom.toFunctor.map_id _) (f.hom.toFunctor.map_id _))

/-- `diagPrecompFst` is a base change of `k`. -/
noncomputable def isTwoFibreProduct_diagPrecompFstSquare :
    Bicategory.IsTwoFibreProduct (diagPrecompFstSquare B S hS k f) :=
  isTwoFibreProduct_of_isTwoFibreProduct_paste_cat B S hS
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f (k ≫ f)))
    (diagPrecompFstSquare B S hS k f)
    (Bicategory.isTwoFibreProduct_of_isEquivalence_from
      (Bicategory.isTwoFibreProduct_swap
        (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
          (k ≫ f) (k ≫ f)))
      (diagPrecompFstPasteHom B S hS k f)
      (inferInstanceAs (Functor.IsEquivalence (𝟭 _))))

/-- `diagPrecompSnd` is a base change of `k`. -/
noncomputable def isTwoFibreProduct_diagPrecompSndSquare :
    Bicategory.IsTwoFibreProduct (diagPrecompSndSquare B S hS k f) :=
  isTwoFibreProduct_of_isTwoFibreProduct_paste_cat B S hS
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} f f)
    (diagPrecompSndSquare B S hS k f)
    (Bicategory.isTwoFibreProduct_of_isEquivalence_from
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        f (k ≫ f))
      (diagPrecompSndPasteHom B S hS k f)
      (inferInstanceAs (Functor.IsEquivalence (𝟭 _))))

/-- The comparison `𝒲 ×_𝒱 𝒲 ⟶ 𝒰 ×_𝒱 𝒰` applying `k` to both factors is étale when `k` is. -/
theorem isRelativelyEtale_diagPrecomp (hk : IsRelativelyEtale B S hS k) :
    IsRelativelyEtale B S hS (diagPrecompFst B S hS k f ≫ diagPrecompSnd B S hS k f) :=
  isRelativelyEtale_comp B S hS _ _
    (isRelativelyEtale_baseChange B S hS _ _ _ k _ (diagPrecompFstSquare B S hS k f)
      (isTwoFibreProduct_diagPrecompFstSquare B S hS k f) hk)
    (isRelativelyEtale_baseChange B S hS _ _ _ k _ (diagPrecompSndSquare B S hS k f)
      (isTwoFibreProduct_diagPrecompSndSquare B S hS k f) hk)

/-- The square `Δ_{k ≫ f}` followed by `k × k` against `k` followed by `Δ_f` 2-commutes, by a
2-isomorphism whose components have identity components. -/
noncomputable def diagPrecompDiagonalIso :
    relativeDiagonal.{u, u, u + 1} B S hS 𝒲 𝒱 (k ≫ f) ≫
        (diagPrecompFst B S hS k f ≫ diagPrecompSnd B S hS k f) ≅
      k ≫ relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒱 f :=
  Bicategory.InducedBicategory.isoMk (BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun x =>
      TwoFibreProductOver.isoMkVertical (U := 𝒲.val.p.obj x) (Iso.refl _) (Iso.refl _)
        (IsHomLift.id (Functor.congr_obj k.hom.w x))
        (IsHomLift.id (Functor.congr_obj k.hom.w x)) (by
          change f.hom.toFunctor.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _ ≫ f.hom.toFunctor.map (𝟙 _)
          simp))
      (fun {x y} φ => by
        refine TwoFibreProductOver.Hom.ext' ?_ ?_ <;>
          change k.hom.toFunctor.map φ ≫ 𝟙 _ = 𝟙 _ ≫ k.hom.toFunctor.map φ <;> simp))
    (fun x => TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 (𝒲.val.p.obj x))
      (IsHomLift.id (Functor.congr_obj k.hom.w x))))

/-- For `k : 𝒲 ⟶ 𝒰` relatively étale and `f : 𝒰 ⟶ 𝒱`, the composite `k ≫ Δ_f : 𝒲 ⟶ 𝒰 ×_𝒱 𝒰` is
relatively étale exactly when the relative diagonal `Δ_{k ≫ f} : 𝒲 ⟶ 𝒲 ×_𝒱 𝒲` is. -/
theorem isRelativelyEtale_comp_relativeDiagonal_iff (hk : IsRelativelyEtale B S hS k) :
    IsRelativelyEtale B S hS (k ≫ relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒱 f) ↔
      IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒲 𝒱 (k ≫ f)) :=
  ⟨fun h => isRelativelyEtale_of_comp B S hS _ _
      (isRelativelyEtale_congr_twoIso B S hS (diagPrecompDiagonalIso B S hS k f).symm h)
      (isRelativelyEtale_diagPrecomp B S hS k f hk),
    fun h => isRelativelyEtale_congr_twoIso B S hS (diagPrecompDiagonalIso B S hS k f)
      (isRelativelyEtale_comp B S hS _ _ h (isRelativelyEtale_diagPrecomp B S hS k f hk))⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
instance hasPullbacks_presheaf_RelativeDiagonalEtalePrecomposition :
    Limits.HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

instance (priority := high) hasPullback_presheaf_RelativeDiagonalEtalePrecomposition
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Limits.HasLimit (Limits.cospan f g) :=
  Limits.HasLimitsOfShape.has_limit _

/-- Let `U` and `V` be algebraic spaces over `S` and `F : 𝒮_U ⟶ 𝒮_V` a 1-morphism of the
associated categories fibred in groupoids, inducing `h : U ⟶ V`. Then the relative diagonal of `F`
is relatively étale exactly when the diagonal `U ⟶ U ×_V U` of `h` is an étale morphism of
algebraic spaces. -/
theorem isRelativelyEtale_relativeDiagonal_iff_isEtale_diagonal
    {U V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hU : IsAlgebraicSpace B S hS U)
    (hV : IsAlgebraicSpace B S hS V) (F : fibredCategory B S hS U ⟶ fibredCategory B S hS V) :
    IsRelativelyEtale B S hS
        (relativeDiagonal.{u, u, u + 1} B S hS (fibredCategory B S hS U)
          (fibredCategory B S hS V) F) ↔
      Space.IsEtale B S hS (Limits.pullback.diagonal
        (representingMap B S hS (fibredCategory B S hS U) (fibredCategory B S hS V) U V
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (StacksRepresentableCFG.EquivalenceOver.refl _) F)) := by
  have hUrep := isRepresentableByAlgebraicSpace_fibredCategory B S hS U hU
  have hFrep : IsRepresentableByAlgebraicSpaces B S hS F.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, u + 1} B S hS
      (isAlgebraicStack_fibredCategory.{u, u + 1} B S hS V hV) hUrep F
  obtain ⟨T, hT, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    (fibredCategory B S hS V) (fibredCategory B S hS U) (fibredCategory B S hS U)
    F.hom F.hom hFrep hUrep
  have hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS (fibredCategory B S hS U)
        (fibredCategory B S hS V) F).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, u + 1} B S hS
      (isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, u + 1} B S hS _ ⟨T, hT, ⟨eT⟩⟩)
      hUrep _
  let _hfib : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS U)
      (fibredCategory B S hS U) (fibredCategory B S hS V) F F).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} F F).pt.property.isFibered
  let : (Space.etaleMorphisms B S hS).RespectsIso :=
    (Space.etaleMorphisms_isStableUnderBaseChange B S hS).respectsIso
  exact (isRelativelyEtale_iff_isEtale_representingMap B S hS _ hΔ U T hU hT
      (StacksRepresentableCFG.EquivalenceOver.refl _) eT).trans
    (prop_representingMap_relativeDiagonal_iff B S hS (fibredCategory B S hS U)
      (fibredCategory B S hS V) F U V (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) T eT (Space.etaleMorphisms B S hS)
      hU hV hT)

/-- For `k : 𝒲 ⟶ 𝒰` relatively étale and relatively surjective and `f : 𝒰 ⟶ 𝒱` with
representable relative diagonal, if `Δ_{k ≫ f}` is relatively étale then so is `Δ_f`. -/
theorem isRelativelyEtale_relativeDiagonal_of_comp (hk : IsRelativelyEtale B S hS k)
    (hksurj : HasRelativeProperty.{u, u, u + 1, u} B S hS (Space.surjectiveMorphismProperty B S hS)
      k hk.1)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒱 f).hom)
    (h : IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒲 𝒱 (k ≫ f))) :
    IsRelativelyEtale B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒱 f) := by
  obtain ⟨-, hcomp⟩ := (isRelativelyEtale_comp_relativeDiagonal_iff B S hS k f hk).2 h
  exact ⟨hΔ, hasRelativeProperty_of_comp_of_cover.{u, u, u + 1, u, u} B S hS
    (Space.etaleMorphisms B S hS) Space.Topology.etale (Or.inl rfl) k
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒱 f) hk.1 hΔ
    (fun U y hy F hF he => ⟨hksurj U y hy F hF he, hk.2 U y hy F hF he⟩) hcomp⟩

end AlgebraicGeometry.Stack

end
