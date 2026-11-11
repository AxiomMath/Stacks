module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceExactness
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuotientStackTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafTensor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidalComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftDualSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictBifunctor

/-!
# The functors `a`, `b`, `c`, `d` of Stacks 0GQS commute with tensor products

Let `f : 𝒰 ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space `U` to an
algebraic stack `𝒳`. Part (9) of Stacks 0GQS says that the functors

```
a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U),   b : LQCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U),
c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U),     d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)
```

of `StacksFrontier.AlgebraicGeometry.Stacks.RestrictionToAlgebraicSpaceQuasicoherent` commute with
tensor products. Each statement here is an isomorphism of bifunctors
`X(ℱ ⊗ 𝒢) ≅ X(ℱ) ⊗ X(𝒢)`, natural in both variables.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.spaceRestrictionTensorIso`: **Stacks 0GQS (9) for
  `a`**, the tensor product of `Mod(𝒳_étale, 𝒪_𝒳)` being the sheafified objectwise tensor product
  `AlgebraicGeometry.FibredSite.sheafTensor` and that of `Mod(U_étale, 𝒪_U)` being
  `AlgebraicGeometry.Space.modulesMonoidalCategory`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSpaceRestrictionTensorIso`: **for `b`**, with the
  tensor product `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohTensor` of `LQCoh(𝒪_𝒳)`, the one of
  `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 06WM (4)), and the tensor product
  `AlgebraicGeometry.Space.quasicoherentSheavesMonoidalCategory` of `QCoh(U_étale, 𝒪_U)`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcSpaceRestrictionTensorIso`: **for `c`**, with
  the tensor product `AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcTensor` of
  `LQCoh^fbc(𝒪_𝒳)`, again the one of `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 0771, through 06WM (4) and
  0764 (5)).
* `AlgebraicGeometry.Stack.AlgebraicStacks.qcohSpaceRestrictionTensorIso`: **for `d`**, with the
  monoidal structure `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesMonoidal` of
  `QCoh(𝒪_𝒳)`, the fppf tensor product sheaf.

## Implementation notes

**The proof for `a`.** `a` is restriction of modules along the continuous and cocontinuous
functor `AlgebraicGeometry.Space.etaleChartToFibred`, with coefficients changed along
`AlgebraicGeometry.Space.etaleChartStructureHom`, an isomorphism on sections. Both tensor products
are sheafified objectwise tensor products; restriction commutes with the objectwise tensor
product because the coefficient map is an isomorphism
(`PresheafOfModules.restrictScalarsTensorObjIso`) and with sheafification because the functor is
cocontinuous (`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`). This is done
once for an arbitrary such functor of ringed sites,
`Stacks.SheafOfModules.pushforwardSheafTensorIso`, with its naturality; the tensor product sheaf
on `U_étale` is then identified with the monoidal product by
`Stacks.SheafOfModules.tensorObjIso`.

**The proofs for `b`, `c`, `d`.** The three categories are full subcategories and the three
functors lifts of `a`. `CategoryTheory.MonoidalCategory.liftTensorBifunctorIso` restricts an
isomorphism of bifunctors to full subcategories stable under the tensor products, which gives `b`
and `c`; `CategoryTheory.MonoidalCategory.liftCompTensorBifunctorIso` precomposes it with a
functor out of a monoidal category carrying its tensor product to the bifunctor, which gives `d`
from the agreement of the fppf and the étale tensor products of quasi-coherent modules,
Stacks 06WN (2), made natural in
`AlgebraicGeometry.FibredSite.sheafTensorSiteAgreement_inv_naturality`.

**Why the general statements.** The structure sheaves of the stack are built by tactic blocks,
and a definitional unfolding of them in a concrete statement is expensive for the elaborator and
the kernel. Every naturality argument is therefore proved where those sheaves are variables, and
the concrete statements are instances whose arguments match on the nose; the tensor product of
`Mod(𝒳_étale, 𝒪_𝒳)` is wrapped in the definition
`AlgebraicGeometry.Stack.AlgebraicStacks.etaleModulesTensor` for the same reason.

## References

* [Stacks Project, Tag 0GQS](https://stacks.math.columbia.edu/tag/0GQS)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace CategoryTheory.MonoidalCategory

variable {C : Type*} [Category C] {D : Type*} [Category D] [MonoidalCategory D]

/-- A family of isomorphisms `A(X ⊗ Y) ≅ A(X) ⊗ A(Y)`, for a bifunctor `T` on `C` and a functor
`A` into a monoidal category, natural in both variables, as an isomorphism of bifunctors. -/
def tensorBifunctorIsoMk (T : C ⥤ C ⥤ C) (A : C ⥤ D)
    (e : ∀ X Y, A.obj ((T.obj X).obj Y) ≅ A.obj X ⊗ A.obj Y)
    (he : ∀ {X X' Y Y'} (φ : X ⟶ X') (ψ : Y ⟶ Y'),
      A.map ((T.map φ).app Y ≫ (T.obj X').map ψ) ≫ (e X' Y').hom =
        (e X Y).hom ≫ (A.map φ ⊗ₘ A.map ψ)) :
    T ⋙ (Functor.whiskeringRight C C D).obj A ≅
      A ⋙ curriedTensor D ⋙ (Functor.whiskeringLeft C D D).obj A :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => e X Y) fun {Y Y'} ψ => by
      have := he (𝟙 X) ψ
      simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
        id_tensorHom] at this
      exact this)
    fun {X X'} φ => by
      ext Y
      have := he φ (𝟙 Y)
      simp only [CategoryTheory.Functor.map_id, Category.comp_id, tensorHom_id] at this
      exact this

section Lift

variable {C : Type*} [Category C] {D : Type*} [Category D] [MonoidalCategory D]
  (P : ObjectProperty C) (Q : ObjectProperty D) [Q.IsMonoidal]
  (T : C ⥤ C ⥤ C) (hT : ∀ X Y, P X → P Y → P ((T.obj X).obj Y))

/-- A bifunctor on `C` which preserves a property `P` of objects, as a bifunctor on the full
subcategory of `P`. -/
def liftBifunctor : P.FullSubcategory ⥤ P.FullSubcategory ⥤ P.FullSubcategory :=
  Functor.curry.obj (ObjectProperty.lift P ((P.ι.prod P.ι) ⋙ Functor.uncurry.obj T)
    fun XY => hT _ _ XY.1.property XY.2.property)

/-- The bifunctor `CategoryTheory.MonoidalCategory.liftBifunctor` is `T` on underlying objects. -/
theorem liftBifunctor_obj_obj_obj (X Y : P.FullSubcategory) :
    (((liftBifunctor P T hT).obj X).obj Y).obj = (T.obj X.obj).obj Y.obj :=
  rfl

/-- The bifunctor `CategoryTheory.MonoidalCategory.liftBifunctor` is `T` on underlying
morphisms. -/
theorem liftBifunctor_map_hom {X X' Y Y' : P.FullSubcategory} (φ : X ⟶ X') (ψ : Y ⟶ Y') :
    (((liftBifunctor P T hT).map φ).app Y ≫ ((liftBifunctor P T hT).obj X').map ψ).hom =
      (T.map φ.hom).app Y.obj ≫ (T.obj X'.obj).map ψ.hom := by
  simp [liftBifunctor]

variable (A : C ⥤ D) (hA : ∀ X, P X → Q (A.obj X))
  (e : ∀ X Y, A.obj ((T.obj X).obj Y) ≅ A.obj X ⊗ A.obj Y)
  (he : ∀ {X X' Y Y'} (φ : X ⟶ X') (ψ : Y ⟶ Y'),
    A.map ((T.map φ).app Y ≫ (T.obj X').map ψ) ≫ (e X' Y').hom =
      (e X Y).hom ≫ (A.map φ ⊗ₘ A.map ψ))

/-- An isomorphism of bifunctors `A(X ⊗ Y) ≅ A(X) ⊗ A(Y)` restricts to full subcategories:
`P` stable under the bifunctor, `Q` a monoidal property, `A` carrying `P` into `Q`. -/
def liftTensorBifunctorIso :
    liftBifunctor P T hT ⋙ (Functor.whiskeringRight _ _ _).obj
        (ObjectProperty.lift Q (P.ι ⋙ A) fun X => hA _ X.property) ≅
      ObjectProperty.lift Q (P.ι ⋙ A) (fun X => hA _ X.property) ⋙
        curriedTensor Q.FullSubcategory ⋙ (Functor.whiskeringLeft _ _ _).obj
          (ObjectProperty.lift Q (P.ι ⋙ A) fun X => hA _ X.property) :=
  tensorBifunctorIsoMk _ _ (fun X Y => Q.fullyFaithfulι.preimageIso (e X.obj Y.obj))
    fun {_ X' _ Y'} φ ψ => Q.fullyFaithfulι.map_injective
      ((congrArg (fun k => A.map k ≫ (e X'.obj Y'.obj).hom)
        (liftBifunctor_map_hom P T hT φ ψ)).trans (he φ.hom ψ.hom))

variable {E : Type*} [Category E] [MonoidalCategory E] (K : E ⥤ C) (hK : ∀ X, P (K.obj X))
  (s : ∀ X Y, K.obj (X ⊗ Y) ≅ (T.obj (K.obj X)).obj (K.obj Y))
  (hs : ∀ {X X' Y Y'} (φ : X ⟶ X') (ψ : Y ⟶ Y'),
    ((T.map (K.map φ)).app (K.obj Y) ≫ (T.obj (K.obj X')).map (K.map ψ)) ≫ (s X' Y').inv =
      (s X Y).inv ≫ K.map (φ ⊗ₘ ψ))

/-- The composite of a functor `K` out of a monoidal category, landing in `P` and carrying its
tensor product to the bifunctor `T` up to natural isomorphism, with the restriction of `A` to
`P`, commutes with tensor products. -/
def liftCompTensorBifunctorIso :
    curriedTensor E ⋙ (Functor.whiskeringRight _ _ _).obj
        (ObjectProperty.lift P K hK ⋙
          ObjectProperty.lift Q (P.ι ⋙ A) fun X => hA _ X.property) ≅
      (ObjectProperty.lift P K hK ⋙
          ObjectProperty.lift Q (P.ι ⋙ A) fun X => hA _ X.property) ⋙
        curriedTensor Q.FullSubcategory ⋙ (Functor.whiskeringLeft _ _ _).obj
          (ObjectProperty.lift P K hK ⋙
            ObjectProperty.lift Q (P.ι ⋙ A) fun X => hA _ X.property) :=
  tensorBifunctorIsoMk _ _
    (fun X Y => Q.fullyFaithfulι.preimageIso (A.mapIso (s X Y) ≪≫ e (K.obj X) (K.obj Y)))
    fun {X X' Y Y'} φ ψ => Q.fullyFaithfulι.map_injective (by
      change A.map (K.map (φ ▷ Y ≫ X' ◁ ψ)) ≫ (A.map (s X' Y').hom ≫ (e _ _).hom) =
        (A.map (s X Y).hom ≫ (e _ _).hom) ≫ (A.map (K.map φ) ⊗ₘ A.map (K.map ψ))
      have hs' : K.map (φ ⊗ₘ ψ) ≫ (s X' Y').hom =
          (s X Y).hom ≫ ((T.map (K.map φ)).app (K.obj Y) ≫ (T.obj (K.obj X')).map (K.map ψ)) := by
        rw [← Iso.inv_comp_eq, ← Category.assoc, ← hs, Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
      rw [← tensorHom_def, ← A.map_comp_assoc, hs', A.map_comp, Category.assoc, he,
        Category.assoc])

end Lift

end CategoryTheory.MonoidalCategory

namespace Stacks.SheafOfModules

universe u₁ v₁ u₂ v₂ r m

/-- **`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso` is natural** in the
presheaf of modules: it commutes with the sheafifications of a morphism and of its restriction. -/
theorem sheafificationRestrictScalarsPushforwardIso_hom_naturality {C : Type u₁}
    [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) (q : C ⥤ D) [q.IsContinuous J K] [q.IsCocontinuous J K]
    (S : Sheaf J RingCat.{r}) (R : Sheaf K RingCat.{r}) (α : S.obj ⟶ q.op ⋙ R.obj)
    [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasWeakSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {M M' : PresheafOfModules.{m} R.obj} (g : M ⟶ M') :
    (PresheafOfModules.sheafification (R := S) (𝟙 S.obj)).map
        ((PresheafOfModules.pushforward₀ q R.obj ⋙ PresheafOfModules.restrictScalars α).map g) ≫
      (sheafificationRestrictScalarsPushforwardIso J K q S R α M').hom =
    (sheafificationRestrictScalarsPushforwardIso J K q S R α M).hom ≫
      ⟨(PresheafOfModules.pushforward₀ q R.obj ⋙ PresheafOfModules.restrictScalars α).map
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map g).val⟩ := by
  let P := PresheafOfModules.pushforward₀ q R.obj ⋙ PresheafOfModules.restrictScalars α
  let L := PresheafOfModules.sheafification.{m} (R := S) (𝟙 S.obj)
  let adjS := PresheafOfModules.sheafificationAdjunction.{m} (R := S) (𝟙 S.obj)
  let adjR := PresheafOfModules.sheafificationAdjunction.{m} (R := R) (𝟙 R.obj)
  let H' : PresheafOfModules.{m} R.obj → SheafOfModules.{m} S := fun N =>
    ⟨P.obj ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj N).val,
      q.op_comp_isSheaf_of_isSheaf J K _
        ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj N).isSheaf⟩
  change L.map (P.map g) ≫ L.map (P.map (adjR.unit.app M')) ≫ adjS.counit.app (H' M') =
    (L.map (P.map (adjR.unit.app M)) ≫ adjS.counit.app (H' M)) ≫ _
  have hn : P.map g ≫ P.map (adjR.unit.app M') =
      P.map (adjR.unit.app M) ≫ P.map ((SheafOfModules.forget R ⋙
        PresheafOfModules.restrictScalars (𝟙 R.obj)).map
          ((PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).map g)) :=
    ((P.map_comp _ _).symm.trans (congrArg P.map (adjR.unit.naturality g))).trans
      (P.map_comp _ _)
  refine (L.map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => L.map k ≫ adjS.counit.app (H' M')) hn).trans ?_
  refine (L.map_comp_assoc _ _ _).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (L.map (P.map (adjR.unit.app M)) ≫ ·) ?_
  exact adjS.counit_naturality (f := (⟨P.map ((PresheafOfModules.sheafification (R := R)
    (𝟙 R.obj)).map g).val⟩ : H' M ⟶ H' M'))

section PushforwardTensor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (q : C ⥤ D)
  [q.IsContinuous J K] [q.IsCocontinuous J K]
  (RC : Sheaf J CommRingCat.{r}) (RD : Sheaf K CommRingCat.{r})
  (φ : Tensor.ringSheaf RC ⟶
    (q.sheafPushforwardContinuous RingCat.{r} J K).obj (Tensor.ringSheaf RD))
  (hφ : ∀ X, IsIso (φ.hom.app X))
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]

include hφ in
/-- A morphism of sheaves of rings `𝒪_C ⟶ q^*𝒪_D` which is an isomorphism on sections, as an
isomorphism of the underlying presheaves of rings. -/
noncomputable def pushforwardStructureIso :
    RC.obj ⋙ forget₂ CommRingCat RingCat ≅ (q.op ⋙ RD.obj) ⋙ forget₂ CommRingCat RingCat :=
  @asIso _ _ _ _ φ.hom (@NatIso.isIso_of_isIso_app _ _ _ _ _ _ φ.hom hφ)

/-- Restriction of presheaves of modules along `q`, with coefficients changed along a morphism
of sheaves of rings which is an isomorphism on sections, commutes with the objectwise tensor
product: `PresheafOfModules.restrictScalarsTensorObjIso`. -/
noncomputable def pushforwardTensorObjIso
    (M N : PresheafOfModules.{r} (Tensor.ringSheaf RD).obj) :
    PresheafOfModules.tensorObj (O := RC.obj)
        ((PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
          PresheafOfModules.restrictScalars φ.hom).obj M)
        ((PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
          PresheafOfModules.restrictScalars φ.hom).obj N) ≅
      (PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
          PresheafOfModules.restrictScalars φ.hom).obj
        (PresheafOfModules.tensorObj (O := RD.obj) M N) :=
  PresheafOfModules.restrictScalarsTensorObjIso RC.obj (q.op ⋙ RD.obj)
    (pushforwardStructureIso J K q RC RD φ hφ) _ _

omit [q.IsCocontinuous J K] [HasWeakSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify K AddCommGrpCat.{r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{r}] in
/-- `Stacks.SheafOfModules.pushforwardTensorObjIso` is natural in both factors. -/
theorem pushforwardTensorObjIso_hom_naturality
    {M M' N N' : PresheafOfModules.{r} (Tensor.ringSheaf RD).obj} (g : M ⟶ M') (g' : N ⟶ N') :
    PresheafOfModules.tensorHom
        ((PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
          PresheafOfModules.restrictScalars φ.hom).map g)
        ((PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
          PresheafOfModules.restrictScalars φ.hom).map g') ≫
      (pushforwardTensorObjIso J K q RC RD φ hφ M' N').hom =
    (pushforwardTensorObjIso J K q RC RD φ hφ M N).hom ≫
      (PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
          PresheafOfModules.restrictScalars φ.hom).map (PresheafOfModules.tensorHom g g') :=
  PresheafOfModules.tensorObj_hom_ext fun _ _ _ => rfl

include hφ in
/-- **Restriction along a continuous and cocontinuous functor of ringed sites, with an
isomorphism of structure sheaves, commutes with the tensor product sheaf.** Both tensor products
are sheafified objectwise tensor products: restriction commutes with the objectwise tensor
product (`Stacks.SheafOfModules.pushforwardTensorObjIso`) and with sheafification
(`Stacks.SheafOfModules.sheafificationRestrictScalarsPushforwardIso`). -/
noncomputable def pushforwardSheafTensorIso
    (F G : _root_.SheafOfModules.{r} (Tensor.ringSheaf RD)) :
    (_root_.SheafOfModules.pushforward φ).obj (((Tensor.sheafTensor RD).obj F).obj G) ≅
      ((Tensor.sheafTensor RC).obj ((_root_.SheafOfModules.pushforward φ).obj F)).obj
        ((_root_.SheafOfModules.pushforward φ).obj G) :=
  (sheafificationRestrictScalarsPushforwardIso J K q (Tensor.ringSheaf RC) (Tensor.ringSheaf RD)
      φ.hom (PresheafOfModules.tensorObj (O := RD.obj) F.val G.val)).symm ≪≫
    (PresheafOfModules.sheafification (R := Tensor.ringSheaf RC)
      (𝟙 (Tensor.ringSheaf RC).obj)).mapIso
      (pushforwardTensorObjIso J K q RC RD φ hφ F.val G.val).symm

/-- `Stacks.SheafOfModules.pushforwardSheafTensorIso` is natural in both factors. -/
theorem pushforwardSheafTensorIso_hom_naturality
    {F F' G G' : _root_.SheafOfModules.{r} (Tensor.ringSheaf RD)} (u : F ⟶ F') (v : G ⟶ G') :
    (_root_.SheafOfModules.pushforward φ).map
        (((Tensor.sheafTensor RD).map u).app G ≫ ((Tensor.sheafTensor RD).obj F').map v) ≫
      (pushforwardSheafTensorIso J K q RC RD φ hφ F' G').hom =
    (pushforwardSheafTensorIso J K q RC RD φ hφ F G).hom ≫
      (((Tensor.sheafTensor RC).map ((_root_.SheafOfModules.pushforward φ).map u)).app
          ((_root_.SheafOfModules.pushforward φ).obj G) ≫
        ((Tensor.sheafTensor RC).obj ((_root_.SheafOfModules.pushforward φ).obj F')).map
          ((_root_.SheafOfModules.pushforward φ).map v)) := by
  let P := PresheafOfModules.pushforward₀ q (Tensor.ringSheaf RD).obj ⋙
    PresheafOfModules.restrictScalars φ.hom
  let L := PresheafOfModules.sheafification.{r} (R := Tensor.ringSheaf RC)
    (𝟙 (Tensor.ringSheaf RC).obj)
  let LD := PresheafOfModules.sheafification.{r} (R := Tensor.ringSheaf RD)
    (𝟙 (Tensor.ringSheaf RD).obj)
  let A := _root_.SheafOfModules.pushforward.{r} φ
  let SI := fun M => sheafificationRestrictScalarsPushforwardIso J K q (Tensor.ringSheaf RC)
    (Tensor.ringSheaf RD) φ.hom M
  let TI := fun M N => pushforwardTensorObjIso J K q RC RD φ hφ M N
  have k1 : ((Tensor.sheafTensor RD).map u).app G ≫ ((Tensor.sheafTensor RD).obj F').map v =
      LD.map (PresheafOfModules.tensorHom u.val v.val) :=
    Tensor.sheafTensor_uncurry_map RD u v
  have k2 : ((Tensor.sheafTensor RC).map (A.map u)).app (A.obj G) ≫
      ((Tensor.sheafTensor RC).obj (A.obj F')).map (A.map v) =
      L.map (PresheafOfModules.tensorHom (P.map u.val) (P.map v.val)) :=
    Tensor.sheafTensor_uncurry_map RC (A.map u) (A.map v)
  have hS : A.map (LD.map (PresheafOfModules.tensorHom u.val v.val)) ≫
      (SI (PresheafOfModules.tensorObj F'.val G'.val)).inv =
      (SI (PresheafOfModules.tensorObj F.val G.val)).inv ≫
        L.map (P.map (PresheafOfModules.tensorHom u.val v.val)) :=
    (Iso.comp_inv_eq _).2 (((Iso.inv_hom_id_assoc _ _).symm.trans (congrArg (_ ≫ ·)
      (sheafificationRestrictScalarsPushforwardIso_hom_naturality J K q (Tensor.ringSheaf RC)
        (Tensor.ringSheaf RD) φ.hom (PresheafOfModules.tensorHom u.val v.val)).symm)).trans
      (Category.assoc _ _ _).symm)
  have hT : P.map (PresheafOfModules.tensorHom u.val v.val) ≫ (TI F'.val G'.val).inv =
      (TI F.val G.val).inv ≫ PresheafOfModules.tensorHom (P.map u.val) (P.map v.val) :=
    (Iso.comp_inv_eq _).2 (((Iso.inv_hom_id_assoc _ _).symm.trans (congrArg (_ ≫ ·)
      (pushforwardTensorObjIso_hom_naturality J K q RC RD φ hφ u.val v.val).symm)).trans
      (Category.assoc _ _ _).symm)
  have hLT := (L.map_comp _ _).symm.trans ((congrArg L.map hT).trans (L.map_comp _ _))
  rw [k1, k2]
  change A.map (LD.map (PresheafOfModules.tensorHom u.val v.val)) ≫
      (SI (PresheafOfModules.tensorObj F'.val G'.val)).inv ≫ L.map (TI F'.val G'.val).inv =
    ((SI (PresheafOfModules.tensorObj F.val G.val)).inv ≫ L.map (TI F.val G.val).inv) ≫
      L.map (PresheafOfModules.tensorHom (P.map u.val) (P.map v.val))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ L.map (TI F'.val G'.val).inv) hS).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) hLT).trans ?_
  exact (Category.assoc _ _ _).symm

end PushforwardTensor

section TensorObjIso

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  (O : Sheaf J CommRingCat.{r})

/-- The identification `Stacks.SheafOfModules.tensorObjIso` of the monoidal product of sheaves of
modules with the tensor product sheaf carries the tensor product sheaf of two morphisms to their
monoidal product. -/
theorem sheafTensor_map_comp_tensorObjIso_inv
    {A A' B B' : _root_.SheafOfModules.{r} (Tensor.ringSheaf O)} (f : A ⟶ A') (g : B ⟶ B') :
    letI := monoidalCategory O.obj (TensorEncodings.isSheaf_structureRingPresheaf O)
    (((Tensor.sheafTensor O).map f).app B ≫ ((Tensor.sheafTensor O).obj A').map g) ≫
      (tensorObjIso O.obj (TensorEncodings.isSheaf_structureRingPresheaf O) A' B').inv =
    (tensorObjIso O.obj (TensorEncodings.isSheaf_structureRingPresheaf O) A B).inv ≫ (f ⊗ₘ g) :=
  letI := monoidalCategory O.obj (TensorEncodings.isSheaf_structureRingPresheaf O)
  have h2 := (Strict.tensorHom_eq_sheafifyMap O.obj
    (TensorEncodings.isSheaf_structureRingPresheaf O) f g).symm.trans
    (Strict.tensorHom_eq_tensorSheafBifunctor_map O f g)
  (Iso.comp_inv_eq _).2 (h2.symm.trans ((Iso.inv_hom_id_assoc _ _).symm.trans
    ((congrArg (_ ≫ ·) (tensorHom_comp_tensorObjIso O.obj
      (TensorEncodings.isSheaf_structureRingPresheaf O) f g).symm).trans
      (Category.assoc _ _ _).symm)))

end TensorObjIso

section TopologyAgreement

variable {C : Type u₁} [Category.{v₁} C] {J K : GrothendieckTopology C} (h : K ≤ J)
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  (R : Sheaf J CommRingCat.{r})
  [HasWeakSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasWeakSheafify K AddCommGrpCat.{m}] [K.WEqualsLocallyBijective AddCommGrpCat.{m}]

omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [K.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
/-- **The agreement of tensor products for two topologies is natural**:
`Stacks.SheafOfModules.tensorLeftAgreement` carries the tensor product, for the coarser topology,
of the readings of two morphisms to the reading of their tensor product for the finer one. -/
theorem tensorLeftAgreement_inv_naturality
    {F F' G G' : _root_.SheafOfModules.{m} (Tensor.ringSheaf (J := J) R)}
    (u : F ⟶ F') (v : G ⟶ G') (hunit) (hunit') :
    (((Tensor.sheafTensor (J := K) (commRingOfLe h R)).map
          ((comparisonPushforward.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)).map u)).app
          ((comparisonPushforward.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)).obj G) ≫
        ((Tensor.sheafTensor (J := K) (commRingOfLe h R)).obj
          ((comparisonPushforward.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)).obj F')).map
          ((comparisonPushforward.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)).map v)) ≫
      (tensorLeftAgreement h R F' G' hunit').inv =
    (tensorLeftAgreement h R F G hunit).inv ≫
      (comparisonPushforward.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)).map
        (((Tensor.sheafTensor (J := J) R).map u).app G ≫
          ((Tensor.sheafTensor (J := J) R).obj F').map v) := by
  let cP := comparisonPushforward.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)
  let cPl := comparisonPullback.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)
  let adj := comparisonAdjunction.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)
  let fact := sheafificationFactorization.{u₁, v₁, r, m} h (Tensor.ringSheaf (J := J) R)
  let LJ := PresheafOfModules.sheafification.{m} (R := Tensor.ringSheaf (J := J) R)
    (𝟙 (Tensor.ringSheaf (J := J) R).obj)
  let LK := PresheafOfModules.sheafification.{m} (R := ringOfLe h (Tensor.ringSheaf (J := J) R))
    (𝟙 (ringOfLe h (Tensor.ringSheaf (J := J) R)).obj)
  let g := PresheafOfModules.tensorHom (O := R.obj) u.val v.val
  have k1 := Tensor.sheafTensor_uncurry_map R u v
  have k2 := Tensor.sheafTensor_uncurry_map (commRingOfLe h R) (cP.map u) (cP.map v)
  refine (congrArg (fun k => k ≫ (tensorLeftAgreement h R F' G' hunit').inv) k2).trans ?_
  refine Eq.trans ?_ (congrArg (fun k => (tensorLeftAgreement h R F G hunit).inv ≫ cP.map k)
    k1).symm
  change LK.map g ≫ adj.unit.app (LK.obj _) ≫ cP.map (fact.inv.app _) =
    (adj.unit.app (LK.obj _) ≫ cP.map (fact.inv.app _)) ≫ cP.map (LJ.map g)
  have hf : cP.map (cPl.map (LK.map g)) ≫ cP.map (fact.inv.app _) =
      cP.map (fact.inv.app _) ≫ cP.map (LJ.map g) :=
    (cP.map_comp _ _).symm.trans ((congrArg cP.map (fact.inv.naturality g)).trans
      (cP.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ cP.map (fact.inv.app _))
    (adj.unit.naturality (LK.map g))).trans ((Category.assoc _ _ _).trans
      ((congrArg (adj.unit.app (LK.obj _) ≫ ·) hf).trans (Category.assoc _ _ _).symm)))

end TopologyAgreement

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U : AlgebraicSpaces B S hS}
  {𝒰 : Type v} [Category.{w} 𝒰] {𝒳 : Type v'} [Category.{w'} 𝒳]
  (p : 𝒰 ⥤ BigFppfOver B S hS) (r : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hr : r.IsFiberedInGroupoids)
  (eU : StacksRepresentableCFG.EquivalenceOver p
    (presheafOfCategories (U.1 ⋙ typeToCat)).p)
  (f : 𝒰 ⥤ 𝒳) (hf : p.IsFibredOneMorphism r f)

attribute [local instance] modulesMonoidalCategory

/-- **Stacks 0GQS (9) for `a`, on objects.** The restriction `a(ℱ) = f^*ℱ|_{U_étale}` of the
tensor product, formed in `Mod(𝒳_étale, 𝒪_𝒳)`, of two `𝒪_𝒳`-modules is the tensor product in
`Mod(U_étale, 𝒪_U)` of their restrictions.

The functor `a` is restriction along the continuous and cocontinuous functor
`AlgebraicGeometry.Space.etaleChartToFibred` with coefficients changed along
`AlgebraicGeometry.Space.etaleChartStructureHom`, an isomorphism on sections, so this is
`Stacks.SheafOfModules.pushforwardSheafTensorIso`, followed by the identification
`AlgebraicGeometry.Space.modulesTensorObjIso` of the tensor product sheaf with the monoidal
product. -/
def etaleRestrictedModuleInverseImageTensorIso
    (F G : inheritedEtaleModules.{u} B S hS r hr) :
    @Iso (Modules.{u, u} B S hS U.1 U.2) _
      ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).obj
        (((FibredSite.sheafTensor B S hS r hr .etale).obj F).obj G))
      ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).obj F ⊗
        (etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).obj G) :=
  letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  letI := isCocontinuous_etaleChartToFibred B S hS p r hp eU f hf
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS r hr .etale
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) :=
      FibredSite.essentiallySmall_over B S hS r hr
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS r .etale))
  Stacks.SheafOfModules.pushforwardSheafTensorIso (SmallEtale.topology B S hS U.1)
      (BigFppfOver.associatedTopology B S hS r .etale) (etaleChartToFibred B S hS p eU f)
      (smallEtaleRingedSite B S hS U.1 U.2).O (FibredSite.structureSheaf B S hS r hr .etale)
      (etaleChartStructureHom B S hS p r hp hr eU f hf)
      (isIso_etaleChartStructureHom_app B S hS p r hp hr eU f hf) F G ≪≫
    (modulesTensorObjIso B S hS U.1 U.2
      ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).obj F)
      ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).obj G)).symm

/-- **Stacks 0GQS (9) for `a`, naturality.** The isomorphism
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageTensorIso` is natural in both factors:
it carries the restriction of the tensor product of two morphisms to the monoidal product of
their restrictions. -/
theorem etaleRestrictedModuleInverseImageTensorIso_hom_naturality
    {F F' G G' : inheritedEtaleModules.{u} B S hS r hr} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).map
        (((FibredSite.sheafTensor B S hS r hr .etale).map φ).app G ≫
          ((FibredSite.sheafTensor B S hS r hr .etale).obj F').map ψ) ≫
      (etaleRestrictedModuleInverseImageTensorIso B S hS p r hp hr eU f hf F' G').hom =
    (etaleRestrictedModuleInverseImageTensorIso B S hS p r hp hr eU f hf F G).hom ≫
      ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).map φ ⊗ₘ
        (etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).map ψ) :=
  letI := etaleChartToFibred_isContinuous B S hS p r hp eU f hf
  letI := isCocontinuous_etaleChartToFibred B S hS p r hp eU f hf
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS r hr .etale
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) :=
      FibredSite.essentiallySmall_over B S hS r hr
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS r .etale))
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (Stacks.SheafOfModules.pushforwardSheafTensorIso_hom_naturality
      (SmallEtale.topology B S hS U.1) (BigFppfOver.associatedTopology B S hS r .etale)
      (etaleChartToFibred B S hS p eU f) (smallEtaleRingedSite B S hS U.1 U.2).O
      (FibredSite.structureSheaf B S hS r hr .etale)
      (etaleChartStructureHom B S hS p r hp hr eU f hf)
      (isIso_etaleChartStructureHom_app B S hS p r hp hr eU f hf) φ ψ)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) (Stacks.SheafOfModules.sheafTensor_map_comp_tensorObjIso_inv
          (smallEtaleRingedSite B S hS U.1 U.2).O
          ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).map φ)
          ((etaleRestrictedModuleInverseImageFunctor B S hS p r hp hr eU f hf).map ψ))).trans
          (Category.assoc _ _ _).symm)))

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The comparison map of sheaves of Stacks 06WC at an étale sheaf of modules is the comparison
map of Stacks 0761: both are the sheafification-adjunct of the comparison map of presheaves. -/
theorem sheafRestrictComparison_app_eq_restrictSheafPullbackComparison {x y : 𝒳} (φ : x ⟶ y)
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    (sheafRestrictComparison B E h S hS p hp φ).app F =
      restrictSheafPullbackComparison B E h S hS p hp φ F :=
  (sheafRestrictComparison_app B E h S hS p hp φ F).trans
    (restrictSheafPullbackComparison_eq B E h S hS p hp φ F).symm

/-- For an étale sheaf of `𝒪_𝒳`-modules, the flat base change property of Stacks 0762 in the
reading of `LQCoh^fbc(𝒪_𝒳)` (the comparison map of presheaves is a local isomorphism) is the
reading through the comparison map of sheaves (it is an isomorphism). -/
theorem hasSheafFlatBaseChangeProperty_iff_hasFlatBaseChangePropertySheafUnivLE
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :
    HasSheafFlatBaseChangeProperty B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F.val ↔
      HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F :=
  (hasSheafFlatBaseChangeProperty_iff_isIso_sheafRestrictComparison B E h S hS p hp F).trans
    ⟨fun H _ _ φ hφ =>
      sheafRestrictComparison_app_eq_restrictSheafPullbackComparison B E h S hS p hp φ F ▸ H φ hφ,
     fun H _ _ φ hφ =>
      (sheafRestrictComparison_app_eq_restrictSheafPullbackComparison B E h S hS p hp φ F).symm ▸
        H φ hφ⟩

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.FibredSite

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

/-- **The agreement of the tensor products of Stacks 06WN (2) is natural.** The isomorphism
`AlgebraicGeometry.FibredSite.sheafTensorSiteAgreement`, between the fppf tensor product read for
a coarser topology and the tensor product for that topology, commutes with the tensor products of
two morphisms of quasi-coherent modules. -/
theorem sheafTensorSiteAgreement_inv_naturality (τ : SiteKind)
    {F F' G G' : quasicoherentModules.{u, v, w, u} B S hS p hp} (φ : F ⟶ F') (ψ : G ⟶ G') :
    (((sheafTensor B S hS p hp τ).map ((toSiteModules B S hS p hp τ).map φ)).app
          ((toSiteModules B S hS p hp τ).obj G) ≫
        ((sheafTensor B S hS p hp τ).obj ((toSiteModules B S hS p hp τ).obj F')).map
          ((toSiteModules B S hS p hp τ).map ψ)) ≫
      (sheafTensorSiteAgreement B S hS p hp τ F' G').inv =
    (sheafTensorSiteAgreement B S hS p hp τ F G).inv ≫
      (Stacks.SheafOfModules.comparisonPushforward.{v, w, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS p τ)
        (ringStructureSheafCore B S hS p hp .fppf)).map
        (((sheafTensor B S hS p hp .fppf).map φ.hom).app G.obj ≫
          ((sheafTensor B S hS p hp .fppf).obj F'.obj).map ψ.hom) :=
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp τ
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS p τ))
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS p hp .fppf
  letI := (haveI : ∀ x : 𝒳, EssentiallySmall.{u} (Over x) := essentiallySmall_over B S hS p hp
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS p .fppf))
  Stacks.SheafOfModules.tensorLeftAgreement_inv_naturality
    (BigFppfOver.associatedTopology_le_fppf B S hS p τ) (structureSheaf B S hS p hp .fppf)
    φ.hom ψ.hom _ _

end AlgebraicGeometry.FibredSite

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)

attribute [local instance] Space.modulesMonoidalCategory
  Space.quasicoherentSheavesMonoidalCategory

/-- The tensor product of `Mod(𝒳_étale, 𝒪_𝒳)`: the sheafification of the objectwise tensor
product, `AlgebraicGeometry.FibredSite.sheafTensor` for the étale topology. -/
def etaleModulesTensor :
    Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⥤
      Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids ⥤
        Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids :=
  FibredSite.sheafTensor B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale

/-- The isomorphism `a(ℱ ⊗ 𝒢) ≅ a(ℱ) ⊗ a(𝒢)` of
`AlgebraicGeometry.Space.etaleRestrictedModuleInverseImageTensorIso` for the functor `a` of
Stacks 0GQS. -/
abbrev spaceRestrictionTensorObjIso
    (F G : Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids) :
    (spaceRestriction B S hS 𝒳 U hU f).obj (((etaleModulesTensor B S hS 𝒳).obj F).obj G) ≅
      (spaceRestriction B S hS 𝒳 U hU f).obj F ⊗ (spaceRestriction B S hS 𝒳 U hU f).obj G :=
  Space.etaleRestrictedModuleInverseImageTensorIso (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) F G

/-- The isomorphism `a(ℱ ⊗ 𝒢) ≅ a(ℱ) ⊗ a(𝒢)` is natural in both factors. -/
theorem spaceRestrictionTensorObjIso_hom_naturality
    {F F' G G' : Space.inheritedEtaleModules.{u} B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids}
    (φ : F ⟶ F') (ψ : G ⟶ G') :
    (spaceRestriction B S hS 𝒳 U hU f).map
        (((etaleModulesTensor B S hS 𝒳).map φ).app G ≫
          ((etaleModulesTensor B S hS 𝒳).obj F').map ψ) ≫
      (spaceRestrictionTensorObjIso B S hS 𝒳 U hU f F' G').hom =
    (spaceRestrictionTensorObjIso B S hS 𝒳 U hU f F G).hom ≫
      ((spaceRestriction B S hS 𝒳 U hU f).map φ ⊗ₘ (spaceRestriction B S hS 𝒳 U hU f).map ψ) :=
  Space.etaleRestrictedModuleInverseImageTensorIso_hom_naturality (U := ⟨U, hU⟩) B S hS
    (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
    (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
    𝒳.val.isFiberedInGroupoids
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (CatFiberedInGroupoids.homFunctor f.hom)
    (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) φ ψ

/-- **Stacks 0GQS (9) for `a`.** The functor `a : Mod(𝒳_étale, 𝒪_𝒳) ⥤ Mod(U_étale, 𝒪_U)`
commutes with tensor products: as bifunctors, `a(ℱ ⊗ 𝒢) ≅ a(ℱ) ⊗ a(𝒢)`, the tensor product on
the left being that of `Mod(𝒳_étale, 𝒪_𝒳)` and on the right that of `Mod(U_étale, 𝒪_U)`. -/
def spaceRestrictionTensorIso :
    etaleModulesTensor B S hS 𝒳 ⋙
        (Functor.whiskeringRight _ _ _).obj (spaceRestriction B S hS 𝒳 U hU f) ≅
      spaceRestriction B S hS 𝒳 U hU f ⋙ curriedTensor (Space.Modules.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (spaceRestriction B S hS 𝒳 U hU f) :=
  MonoidalCategory.tensorBifunctorIsoMk _ _ (spaceRestrictionTensorObjIso B S hS 𝒳 U hU f)
    (spaceRestrictionTensorObjIso_hom_naturality B S hS 𝒳 U hU f)

theorem isLocallyQuasicoherent_etaleModulesTensor (F G : lqcohModules B S hS 𝒳) :
    Stack.isLocallyQuasicoherent B (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids (((etaleModulesTensor B S hS 𝒳).obj F.obj).obj G.obj) :=
  letI := Stack.hasSheafify_associatedTopology_siteKind B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids .etale
  letI := (haveI : ∀ x : 𝒳.val.val.obj, EssentiallySmall.{u} (Over x) :=
      FibredSite.essentiallySmall_over B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat_of_essentiallySmall_over.{u}
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p .etale))
  Stack.isLocallyQuasicoherent_etaleTensorSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
    (associatedBigEtaleSite B) rfl F.obj G.obj F.property G.property

/-- The tensor product of `LQCoh(𝒪_𝒳)`: the tensor product of `Mod(𝒳_étale, 𝒪_𝒳)`, which
keeps local quasi-coherence by Stacks 06WM (4)
(`AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasicoherent_etaleModulesTensor`). -/
def lqcohTensor : lqcohModules B S hS 𝒳 ⥤ lqcohModules B S hS 𝒳 ⥤ lqcohModules B S hS 𝒳 :=
  MonoidalCategory.liftBifunctor _ (etaleModulesTensor B S hS 𝒳)
    fun F G hF hG => isLocallyQuasicoherent_etaleModulesTensor B S hS 𝒳 ⟨F, hF⟩ ⟨G, hG⟩

/-- **Stacks 0GQS (9) for `b`.** The functor `b : LQCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` commutes
with tensor products: as bifunctors, `b(ℱ ⊗ 𝒢) ≅ b(ℱ) ⊗ b(𝒢)`, the tensor product on the left
being that of `LQCoh(𝒪_𝒳)` (`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohTensor`) and on the
right that of `QCoh(U_étale, 𝒪_U)`. -/
def lqcohSpaceRestrictionTensorIso :
    lqcohTensor B S hS 𝒳 ⋙
        (Functor.whiskeringRight _ _ _).obj (lqcohSpaceRestriction B S hS 𝒳 U hU f) ≅
      lqcohSpaceRestriction B S hS 𝒳 U hU f ⋙
        curriedTensor (Space.QuasicoherentSheaves.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (lqcohSpaceRestriction B S hS 𝒳 U hU f) :=
  MonoidalCategory.liftTensorBifunctorIso _ _ (etaleModulesTensor B S hS 𝒳)
    (fun F G hF hG => isLocallyQuasicoherent_etaleModulesTensor B S hS 𝒳 ⟨F, hF⟩ ⟨G, hG⟩)
    (spaceRestriction B S hS 𝒳 U hU f)
    (fun F hF =>
      Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
        B (associatedBigEtaleSite B) rfl S hS (U := ⟨U, hU⟩)
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
        (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (CatFiberedInGroupoids.homFunctor f.hom)
        (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) F hF)
    (spaceRestrictionTensorObjIso B S hS 𝒳 U hU f)
    (spaceRestrictionTensorObjIso_hom_naturality B S hS 𝒳 U hU f)

/-! ### The functor `c` -/

/-- **`LQCoh^fbc(𝒪_𝒳)` is closed under the tensor product of `Mod(𝒳_étale, 𝒪_𝒳)`** (Stacks 0771):
local quasi-coherence is kept by Stacks 06WM (4), and the flat base change property by
Stacks 0764 (5) (`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_tensor`). -/
theorem lqcohSheafFbcEtaleModules_etaleModulesTensor (F G : lqcohFbcModules B S hS 𝒳) :
    lqcohSheafFbcEtaleModules.{u, w, u} B (associatedBigEtaleSite B) rfl S hS 𝒳
      (((etaleModulesTensor B S hS 𝒳).obj F.obj).obj G.obj) :=
  ⟨isLocallyQuasicoherent_etaleModulesTensor B S hS 𝒳 ⟨F.obj, F.property.1⟩ ⟨G.obj, G.property.1⟩,
    (Stack.hasSheafFlatBaseChangeProperty_iff_hasFlatBaseChangePropertySheafUnivLE B
      (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids _).2
      (Stack.hasFlatBaseChangePropertySheaf_tensor B (associatedBigEtaleSite B) rfl S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids F.obj G.obj
        ((Stack.hasSheafFlatBaseChangeProperty_iff_hasFlatBaseChangePropertySheafUnivLE B
          (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          F.obj).1 F.property.2)
        ((Stack.hasSheafFlatBaseChangeProperty_iff_hasFlatBaseChangePropertySheafUnivLE B
          (associatedBigEtaleSite B) rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          G.obj).1 G.property.2))⟩

/-- The tensor product of `LQCoh^fbc(𝒪_𝒳)`: the tensor product of `Mod(𝒳_étale, 𝒪_𝒳)`, which
keeps `LQCoh^fbc(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohSheafFbcEtaleModules_etaleModulesTensor`). -/
def lqcohFbcTensor :
    lqcohFbcModules B S hS 𝒳 ⥤ lqcohFbcModules B S hS 𝒳 ⥤ lqcohFbcModules B S hS 𝒳 :=
  MonoidalCategory.liftBifunctor _ (etaleModulesTensor B S hS 𝒳)
    fun F G hF hG => lqcohSheafFbcEtaleModules_etaleModulesTensor B S hS 𝒳 ⟨F, hF⟩ ⟨G, hG⟩

/-- **Stacks 0GQS (9) for `c`.** The functor `c : LQCoh^fbc(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)`
commutes with tensor products: as bifunctors, `c(ℱ ⊗ 𝒢) ≅ c(ℱ) ⊗ c(𝒢)`, the tensor product on
the left being that of `LQCoh^fbc(𝒪_𝒳)`
(`AlgebraicGeometry.Stack.AlgebraicStacks.lqcohFbcTensor`) and on the right that of
`QCoh(U_étale, 𝒪_U)`. -/
def lqcohFbcSpaceRestrictionTensorIso :
    lqcohFbcTensor B S hS 𝒳 ⋙
        (Functor.whiskeringRight _ _ _).obj (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) ≅
      lqcohFbcSpaceRestriction B S hS 𝒳 U hU f ⋙
        curriedTensor (Space.QuasicoherentSheaves.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (lqcohFbcSpaceRestriction B S hS 𝒳 U hU f) :=
  MonoidalCategory.liftTensorBifunctorIso _ _ (etaleModulesTensor B S hS 𝒳)
    (fun F G hF hG => lqcohSheafFbcEtaleModules_etaleModulesTensor B S hS 𝒳 ⟨F, hF⟩ ⟨G, hG⟩)
    (spaceRestriction B S hS 𝒳 U hU f)
    (fun F hF =>
      Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
        B (associatedBigEtaleSite B) rfl S hS (U := ⟨U, hU⟩)
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
        (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (CatFiberedInGroupoids.homFunctor f.hom)
        (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) F hF.1)
    (spaceRestrictionTensorObjIso B S hS 𝒳 U hU f)
    (spaceRestrictionTensorObjIso_hom_naturality B S hS 𝒳 U hU f)

/-! ### The functor `d` -/

section QCoh

attribute [local instance] hasSheafCompose_forget_ringCat
  hasSheafCompose_forget_commRingCat Stacks.hasSheafCompose_forget₂_commRingCat
  FlatFppf.hasSheafify_addCommGrpCat FlatFppf.wEqualsLocallyBijective_addCommGrpCat
  FlatFppf.hasSheafify_fppf_addCommGrpCat FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat
  FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

attribute [local instance] quasicoherentModulesMonoidal

/-- The tensor product in `QCoh(𝒪_𝒳)` of two morphisms is the tensor product sheaf of the two
morphisms, `AlgebraicGeometry.FibredSite.sheafTensor` for the fppf topology. -/
theorem quasicoherentModules_tensorHom_hom {F F' G G' : quasicoherentModules B S hS 𝒳}
    (φ : F ⟶ F') (ψ : G ⟶ G') :
    (φ ⊗ₘ ψ).hom =
      ((FibredSite.sheafTensor B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).map
          φ.hom).app G.obj ≫
        ((FibredSite.sheafTensor B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf).obj
          F'.obj).map ψ.hom :=
  Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map
    (FlatFppf.fppfRingedTopos B S hS 𝒳).O φ.hom ψ.hom

/-- The reading on the étale site of the tensor product of `QCoh(𝒪_𝒳)` is the tensor product of
`Mod(𝒳_étale, 𝒪_𝒳)` of the readings: Stacks 06WN (2),
`AlgebraicGeometry.FibredSite.sheafTensorSiteAgreement`. -/
def qcohToSiteTensorIso (X Y : quasicoherentModules B S hS 𝒳) :
    (FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj
        (X ⊗ Y) ≅
      ((etaleModulesTensor B S hS 𝒳).obj
        ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj X)).obj
        ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj Y) :=
  FibredSite.sheafTensorSiteAgreement B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale X Y

/-- `AlgebraicGeometry.Stack.AlgebraicStacks.qcohToSiteTensorIso` is natural in both factors. -/
theorem qcohToSiteTensorIso_inv_naturality {F F' G G' : quasicoherentModules B S hS 𝒳}
    (φ : F ⟶ F') (ψ : G ⟶ G') :
    (((etaleModulesTensor B S hS 𝒳).map
          ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).map
            φ)).app
          ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj
            G) ≫
        ((etaleModulesTensor B S hS 𝒳).obj
          ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).obj
            F')).map
          ((FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).map
            ψ)) ≫
      (qcohToSiteTensorIso B S hS 𝒳 F' G').inv =
    (qcohToSiteTensorIso B S hS 𝒳 F G).inv ≫
      (FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale).map
        (φ ⊗ₘ ψ) :=
  (FibredSite.sheafTensorSiteAgreement_inv_naturality B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids .etale φ ψ).trans
    (congrArg (fun k => (qcohToSiteTensorIso B S hS 𝒳 F G).inv ≫
      (Stacks.SheafOfModules.comparisonPushforward.{u + 1, u, u, u}
        (BigFppfOver.associatedTopology_le_fppf B S hS 𝒳.val.val.p .etale)
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
          .fppf)).map k) (quasicoherentModules_tensorHom_hom B S hS 𝒳 φ ψ).symm)

/-- The isomorphism of bifunctors of
`AlgebraicGeometry.Stack.AlgebraicStacks.qcohSpaceRestrictionTensorIso`, for the functor `d`
spelled as in `AlgebraicGeometry.Stack.AlgebraicStacks.qcohSpaceRestriction_eq_lift`. -/
def qcohSpaceRestrictionLiftTensorIso :=
  MonoidalCategory.liftCompTensorBifunctorIso _ _ (etaleModulesTensor B S hS 𝒳)
    (spaceRestriction B S hS 𝒳 U hU f)
    (fun F hF =>
      Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
        B (associatedBigEtaleSite B) rfl S hS (U := ⟨U, hU⟩)
        (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
        (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (CatFiberedInGroupoids.homFunctor f.hom)
        (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) F hF)
    (spaceRestrictionTensorObjIso B S hS 𝒳 U hU f)
    (spaceRestrictionTensorObjIso_hom_naturality B S hS 𝒳 U hU f)
    (FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)
    (fun X => Stack.isLocallyQuasicoherent_toSiteModules_etale B (associatedBigEtaleSite B) rfl
      S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids X)
    (qcohToSiteTensorIso B S hS 𝒳) (qcohToSiteTensorIso_inv_naturality B S hS 𝒳)

/-- The functor `d` is the restriction of `a` along the reading on the étale site, with both
inclusions into full subcategories spelled as lifts. -/
theorem qcohSpaceRestriction_eq_lift :
    qcohSpaceRestriction B S hS 𝒳 U hU f =
      (ObjectProperty.lift _
        (FibredSite.toSiteModules B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .etale)
        (fun X => Stack.isLocallyQuasicoherent_toSiteModules_etale B (associatedBigEtaleSite B)
          rfl S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids X) :
        quasicoherentModules B S hS 𝒳 ⥤ lqcohModules B S hS 𝒳) ⋙
      (ObjectProperty.lift _ (lqcohInclusion B S hS 𝒳 ⋙ spaceRestriction B S hS 𝒳 U hU f)
        (fun F =>
          Space.isQuasicoherentOnSite_etaleRestrictedModuleInverseImage_of_isLocallyQuasicoherent
          B (associatedBigEtaleSite B) rfl S hS (U := ⟨U, hU⟩)
          (algebraicSpaceStack.{u, w} B S hS U hU).val.val.p 𝒳.val.val.p
          (algebraicSpaceStack.{u, w} B S hS U hU).val.isFiberedInGroupoids
          𝒳.val.isFiberedInGroupoids
          (StacksRepresentableCFG.EquivalenceOver.refl _)
          (CatFiberedInGroupoids.homFunctor f.hom)
          (BigFppfOver.isFibredOneMorphism_homFunctor B S hS f.hom) F.obj F.property) :
        lqcohModules B S hS 𝒳 ⥤ Space.QuasicoherentSheaves.{u, u} B S hS U hU) :=
  rfl

/-- **Stacks 0GQS (9) for `d`.** The functor `d : QCoh(𝒪_𝒳) ⥤ QCoh(U_étale, 𝒪_U)` commutes with
tensor products: as bifunctors, `d(ℱ ⊗ 𝒢) ≅ d(ℱ) ⊗ d(𝒢)`, the tensor product on the left being
that of `QCoh(𝒪_𝒳)` (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentModulesMonoidal`) and
on the right that of `QCoh(U_étale, 𝒪_U)`.

The tensor product of `QCoh(𝒪_𝒳)` is formed on the fppf site, and its reading on the étale site
is the tensor product of `Mod(𝒳_étale, 𝒪_𝒳)` of the readings, naturally, by Stacks 06WN (2)
(`AlgebraicGeometry.FibredSite.sheafTensorSiteAgreement` and
`AlgebraicGeometry.FibredSite.sheafTensorSiteAgreement_inv_naturality`); then `d` is `a`. -/
def qcohSpaceRestrictionTensorIso :
    curriedTensor (quasicoherentModules B S hS 𝒳) ⋙
        (Functor.whiskeringRight _ _ _).obj (qcohSpaceRestriction B S hS 𝒳 U hU f) ≅
      qcohSpaceRestriction B S hS 𝒳 U hU f ⋙
        curriedTensor (Space.QuasicoherentSheaves.{u, u} B S hS U hU) ⋙
        (Functor.whiskeringLeft _ _ _).obj (qcohSpaceRestriction B S hS 𝒳 U hU f) := by
  rw [qcohSpaceRestriction_eq_lift]
  exact qcohSpaceRestrictionLiftTensorIso B S hS 𝒳 U hU f

end QCoh

end AlgebraicGeometry.Stack.AlgebraicStacks

end
