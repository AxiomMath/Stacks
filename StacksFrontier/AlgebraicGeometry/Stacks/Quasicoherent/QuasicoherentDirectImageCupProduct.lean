module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DegreeZeroCupProductAndCoherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.StructureSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentDirectImage
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteLocalization
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms

import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product of quasi-coherent direct images (Stacks 0GQR)

Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of algebraic stacks and let
`𝓕`, `𝓖` be quasi-coherent `𝒪_𝒳`-modules. **Stacks 0GQR** says that there is a canonical
commutative diagram

```
f_{QCoh,*}𝓕 ⊗ f_{QCoh,*}𝓖 ───→ f_*𝓕 ⊗ f_*𝓖
        │                              │ c
        ↓                              ↓
f_{QCoh,*}(𝓕 ⊗ 𝓖) ─────────→ f_*(𝓕 ⊗ 𝓖)
```

in which `c` is the naive relative cup product in degree `0` (Stacks 0FPJ), the left vertical
arrow is `Q(c)` read through the compatibility of the coherator `Q` with tensor products
(Remark 0GQM), the horizontal arrows are the counits `Q(-) ⟶ (-)` of the coherator, and the
construction is functorial in `𝓕` and `𝓖`.

Here `f_*` is the direct image of the morphism of ringed topoi that `f` induces on the fppf sites
(Stacks 06TW, `AlgebraicGeometry.FibredSite.ringedToposMorphism`), `c` is built from the adjunction
`f^* ⊣ f_*` (Stacks 03D7) and the comparison `f^*(A ⊗ B) ≅ f^*A ⊗ f^*B` (Stacks 03EL), the tensor
products are the sheafified tensor products of sheaves of modules, the tensor product of `QCoh(𝒪)`
is that tensor product, which is quasi-coherent by Stacks 0GQM, so that the inclusion
`i : QCoh(𝒪) ⥤ Mod(𝒪)` carries it to the tensor product of modules on the nose, and `Q` is the
coherator of an algebraic stack, `AlgebraicGeometry.Stack.AlgebraicStacks.coherator` (Stacks 0781
(2), whose restriction to `LQCoh^fbc` is the coherator of Stacks 0778), which takes no input: all
five inputs of the special adjoint functor theorem are proved, the separator being
`AlgebraicGeometry.Stack.hasSeparator_quasicoherentModules`.

## Main definitions

* `AlgebraicGeometry.FibredSite.quasicoherentSheafTensor`: the tensor product of `QCoh(𝒪_𝒳)`.
* `AlgebraicGeometry.FibredSite.directImageNaiveCupProduct`: the arrow `c`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentCupProduct`: the left vertical arrow.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.map_quasicoherentCupProduct_comp_counit`:
  **Stacks 0GQR**, the diagram commutes, for a quasi-compact quasi-separated 1-morphism of
  algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentCupProduct_natural` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentNaiveCupProduct_natural`:
  **Stacks 0GQR**, functoriality in `𝓕` and `𝓖`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentCupProduct_eq`: the left vertical arrow
  is the comparison of Remark 0GQM followed by `Q(c)`.

## Implementation notes

*The middle category.* The source applies the coherator of Stacks 0778 to `c`, which is a map in
`LQCoh^fbc(𝒪_𝒴)` by Stacks 0771; it is quasi-compactness and quasi-separatedness of `f` that put
`f_*𝓕` there. Here `c` is a map of `Mod(𝒪_𝒴)` and `Q` is the coherator on all of `Mod(𝒪_𝒴)`,
whose restriction to `LQCoh^fbc` is the one of 0778 (both are the right adjoint of an inclusion of
`QCoh(𝒪_𝒴)`). This is the reading of `f_{QCoh,*} = Q ∘ f_* ∘ i` the library takes for
Stacks 077A too (`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentDirectImage`, which is
built on the direct image of modules `AlgebraicGeometry.Stack.fppfModulesPushforward`; here `f_*`
is the direct image of the morphism of ringed topoi of Stacks 06TW, because the naive cup product
`c` of Stacks 0FPJ is defined from that morphism's `f^* ⊣ f_*` and its tensor comparison). The
diagram then commutes for every 1-morphism; the hypotheses on `f` are kept in the statements
because they are the source's.

*The left vertical arrow.* The source obtains it as `Q(c)` composed with the inverse of the
isomorphism `Q(f_*𝓕) ⊗ Q(f_*𝓖) ≅ Q(f_*𝓕 ⊗ f_*𝓖)` of Remark 0GQM. That isomorphism is the
canonical comparison `μ` of the coherator, lax monoidal as the right adjoint of the monoidal
inclusion of `QCoh(𝒪_𝒴)` (Stacks 0GQM (iii)), and `quasicoherentCupProduct_eq` records that the
left arrow is exactly that map followed by `Q(c)`. The commutativity and the functoriality do
not use that the comparison is invertible; its invertibility on `LQCoh^fbc(𝒪_𝒴)` is Stacks 0GQM
(iv), `AlgebraicGeometry.Stack.AlgebraicStacks.isIso_coheratorTensorComparison`.

*Universes.* The tensor product of sheaves of modules on the fppf site exists at the universe
`u` of the structure sheaf, and so does the direct image of the morphism of ringed topoi of
Stacks 06TW (the site being essentially `u`-small); everything is seated there.

## References

* [Stacks Project, Tag 0GQR](https://stacks.math.columbia.edu/tag/0GQR)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 0FPJ](https://stacks.math.columbia.edu/tag/0FPJ)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0781](https://stacks.math.columbia.edu/tag/0781)
* [Stacks Project, Tag 077A](https://stacks.math.columbia.edu/tag/077A)
* [Stacks Project, Tag 06TW](https://stacks.math.columbia.edu/tag/06TW)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Prod

universe u w

namespace AlgebraicGeometry.FibredSite

attribute [local instance] hasSheafCompose_forget_ringCat
  Stacks.hasSheafCompose_forget₂_commRingCat

section Instances

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The sheaf condition for abelian groups is preserved by the forgetful functor on the
associated ringed topos of a category fibred in groupoids, which preserves limits of every
size. -/
theorem hasSheafCompose_forget_addCommGrpCat_associatedRingedTopos (τ : SiteKind) :
    (associatedRingedTopos B S hS p hp τ).J.HasSheafCompose (forget AddCommGrpCat.{u}) :=
  hasSheafCompose_of_preservesLimitsOfSize _

variable [EssentiallySmall.{u} 𝒳] in
/-- Abelian sheaves on the associated ringed topos can be sheafified at the universe of the
structure sheaf: the site is essentially small. -/
theorem hasWeakSheafify_associatedRingedTopos (τ : SiteKind) :
    HasWeakSheafify (associatedRingedTopos B S hS p hp τ).J AddCommGrpCat.{u} :=
  hasWeakSheafify_associatedTopology B S hS p τ

variable [EssentiallySmall.{u} 𝒳] in
/-- On the associated ringed topos the local isomorphisms of abelian presheaves are the locally
bijective morphisms. -/
theorem wEqualsLocallyBijective_associatedRingedTopos (τ : SiteKind) :
    (associatedRingedTopos B S hS p hp τ).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_associatedTopology B S hS p τ

end Instances

attribute [local instance] hasSheafCompose_forget_addCommGrpCat_associatedRingedTopos
  hasWeakSheafify_associatedRingedTopos wEqualsLocallyBijective_associatedRingedTopos

section Tensor

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

attribute [local instance] hasWeakSheafify_associatedTopology
  wEqualsLocallyBijective_associatedTopology

/-- The inclusion `i : QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)` of Stacks 06WG at module universe `u`. -/
abbrev quasicoherentModulesInclusion :
    quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) :=
  (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
    (ringStructureSheafCore B S hS p hp .fppf)).ι

/-- The tensor product `⊗_{𝒪_𝒳}` of sheaves of modules on the fppf site, the sheafification of
the objectwise tensor product (Stacks 01CA), as a functor on pairs. -/
abbrev fppfSheafTensor :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ×
        SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) :=
  Functor.uncurry.obj
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (associatedRingedTopos B S hS p hp .fppf).O)

/-- **The tensor product of `QCoh(𝒪_𝒳)`**: the tensor product of sheaves of modules, which is
quasi-coherent on quasi-coherent inputs by Stacks 0GQM
(`AlgebraicGeometry.FibredSite.isQuasicoherentOnSite_tensorSheaf`). -/
abbrev quasicoherentSheafTensor :
    quasicoherentModules.{u, u + 1, u, u} B S hS p hp ×
        quasicoherentModules.{u, u + 1, u, u} B S hS p hp ⥤
      quasicoherentModules.{u, u + 1, u, u} B S hS p hp :=
  ObjectProperty.lift _
    ((quasicoherentModulesInclusion B S hS p hp).prod (quasicoherentModulesInclusion B S hS p hp) ⋙
      fppfSheafTensor B S hS p hp)
    (fun FG => by
      have : FG.1.obj.IsQuasicoherentOnSite := FG.1.property
      have : FG.2.obj.IsQuasicoherentOnSite := FG.2.property
      exact isQuasicoherentOnSite_tensorSheaf B S hS p hp .fppf FG.1.obj FG.2.obj)

/-- **The inclusion `i` is compatible with tensor products**: `i(𝓕 ⊗ 𝓖) = i𝓕 ⊗ i𝓖`, with
identity components. -/
def quasicoherentSheafTensorCompInclusionIso :
    quasicoherentSheafTensor B S hS p hp ⋙ quasicoherentModulesInclusion B S hS p hp ≅
      (quasicoherentModulesInclusion B S hS p hp).prod (quasicoherentModulesInclusion B S hS p hp) ⋙
        fppfSheafTensor B S hS p hp :=
  ObjectProperty.liftCompιIso _ _ _

end Tensor

section CupProduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  {𝒴 : Type (u + 1)} [Category.{u} 𝒴] [EssentiallySmall.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒳 ⥤ 𝒴) (hF : p.IsFibredOneMorphism q F)

attribute [local instance] hasWeakSheafify_associatedTopology
  wEqualsLocallyBijective_associatedTopology

/-- The morphism of ringed topoi `(Sh(𝒳_fppf), 𝒪_𝒳) ⟶ (Sh(𝒴_fppf), 𝒪_𝒴)` induced by a
1-morphism `F` (Stacks 06TW), in the form the module functors of Stacks 03D6 take. -/
def fppfModulesRingedToposHom :
    Stacks.Sheaves.RingedToposModules.RingedToposHom
      (associatedRingedTopos B S hS p hp .fppf) (associatedRingedTopos B S hS q hq .fppf) :=
  haveI := fun G => Stack.hasPointwiseRightKanExtension_op F G
  (ringedToposMorphism B S hS p q hp hq F hF .fppf).toModulesHom

/-- The direct image `f_*` of sheaves of modules (Stacks 03D6). -/
abbrev fppfPushforwardModules :
    SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS q hq .fppf) :=
  Stacks.Sheaves.RingedToposModules.pushforwardModules
    (X := associatedRingedTopos B S hS p hp .fppf) (Y := associatedRingedTopos B S hS q hq .fppf)
    (fppfModulesRingedToposHom B S hS p q hp hq F hF)

/-- The inverse image `f^*` of sheaves of modules (Stacks 03D6). -/
abbrev fppfPullbackModules :
    SheafOfModules.{u} (ringStructureSheafCore B S hS q hq .fppf) ⥤
      SheafOfModules.{u} (ringStructureSheafCore B S hS p hp .fppf) :=
  (fppfModulesRingedToposHom B S hS p q hp hq F hF).pullbackModules

/-- The adjunction `f^* ⊣ f_*` of Stacks 03D7. -/
abbrev fppfModulesAdjunction :
    fppfPullbackModules B S hS p q hp hq F hF ⊣ fppfPushforwardModules B S hS p q hp hq F hF :=
  Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    (fppfModulesRingedToposHom B S hS p q hp hq F hF)

/-- The comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` of Stacks 03EL. -/
abbrev fppfPullbackTensorComparison :
    fppfSheafTensor B S hS q hq ⋙ fppfPullbackModules B S hS p q hp hq F hF ⟶
      (fppfPullbackModules B S hS p q hp hq F hF).prod (fppfPullbackModules B S hS p q hp hq F hF) ⋙
        fppfSheafTensor B S hS p hp :=
  (Stacks.SheafOfModules.pullbackTensorIso (fppfModulesRingedToposHom B S hS p q hp hq F hF)).hom

/-- **The naive relative cup product in degree `0`** (Stacks 0FPJ), the right vertical arrow `c`
of Stacks 0GQR: `f_*𝓕 ⊗ f_*𝓖 ⟶ f_*(𝓕 ⊗ 𝓖)`, adjoint to the comparison of Stacks 03EL
followed by the counit of `f^* ⊣ f_*` in each factor. It is
`Stacks.Cohomology.DegreeZeroCupProduct.naiveRelativeCupProduct` at this morphism of ringed
topoi. -/
@[stacks 0GQR "the vertical arrow c on the right, the naive relative cup product in degree 0"]
def directImageNaiveCupProduct (M N : quasicoherentModules.{u, u + 1, u, u} B S hS p hp) :
    (fppfSheafTensor B S hS q hq).obj
        ((fppfPushforwardModules B S hS p q hp hq F hF).obj
            ((quasicoherentModulesInclusion B S hS p hp).obj M),
          (fppfPushforwardModules B S hS p q hp hq F hF).obj
            ((quasicoherentModulesInclusion B S hS p hp).obj N)) ⟶
      (fppfPushforwardModules B S hS p q hp hq F hF).obj
        ((quasicoherentModulesInclusion B S hS p hp).obj
          ((quasicoherentSheafTensor B S hS p hp).obj (M, N))) :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
    (fppfModulesAdjunction B S hS p q hp hq F hF)
    (fppfSheafTensor B S hS q hq) (fppfSheafTensor B S hS p hp)
    (fppfPullbackTensorComparison B S hS p q hp hq F hF) M.obj N.obj

/-- `c` is natural in the two modules. -/
theorem directImageNaiveCupProduct_natural
    {M M' N N' : quasicoherentModules.{u, u + 1, u, u} B S hS p hp}
    (a : M ⟶ M') (b : N ⟶ N') :
    (fppfSheafTensor B S hS q hq).map
        ((fppfPushforwardModules B S hS p q hp hq F hF).map
            ((quasicoherentModulesInclusion B S hS p hp).map a) ×ₘ
          (fppfPushforwardModules B S hS p q hp hq F hF).map
            ((quasicoherentModulesInclusion B S hS p hp).map b)) ≫
      directImageNaiveCupProduct B S hS p q hp hq F hF M' N' =
    directImageNaiveCupProduct B S hS p q hp hq F hF M N ≫
      (fppfPushforwardModules B S hS p q hp hq F hF).map
        ((quasicoherentModulesInclusion B S hS p hp).map
          ((quasicoherentSheafTensor B S hS p hp).map (a ×ₘ b))) :=
  Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_natural
    (fppfModulesAdjunction B S hS p q hp hq F hF)
    (fppfSheafTensor B S hS q hq) (fppfSheafTensor B S hS p hp)
    (fppfPullbackTensorComparison B S hS p q hp hq F hF) a.hom b.hom

end CupProduct

end AlgebraicGeometry.FibredSite

/-! ### The diagram of Stacks 0GQR for a 1-morphism of algebraic stacks -/

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- The inclusion `QCoh(𝒪_𝒳) ⥤ Mod(𝒪_𝒳)`. -/
local notation "i𝒳" =>
  FibredSite.quasicoherentModulesInclusion B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
/-- The inclusion `QCoh(𝒪_𝒴) ⥤ Mod(𝒪_𝒴)`. -/
local notation "i𝒴" => quasicoherentInclusion B S hS 𝒴
/-- The tensor product of `QCoh(𝒪_𝒳)`. -/
local notation "tensorQ𝒳" =>
  FibredSite.quasicoherentSheafTensor B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
/-- The tensor product of `QCoh(𝒪_𝒴)`. -/
local notation "tensorQ𝒴" =>
  FibredSite.quasicoherentSheafTensor B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
/-- The tensor product of `Mod(𝒪_𝒴)`. -/
local notation "tensor𝒴" =>
  FibredSite.fppfSheafTensor B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
/-- `i(𝓕 ⊗ 𝓖) = i𝓕 ⊗ i𝓖` on `𝒴`. -/
local notation "tensorIso𝒴" =>
  FibredSite.quasicoherentSheafTensorCompInclusionIso B S hS 𝒴.val.val.p
    𝒴.val.isFiberedInGroupoids
/-- `f_*`. -/
local notation "fStar" =>
  FibredSite.fppfPushforwardModules B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism f.hom.hom.w)
/-- The coherator `Q` of `𝒴`. -/
local notation "Q𝒴" => coherator B S hS 𝒴
/-- The coherator adjunction `i ⊣ Q` on `𝒴`. -/
local notation "adjQ" => coheratorAdjunction B S hS 𝒴
/-- `f_{QCoh,*} = Q ∘ f_* ∘ i`. -/
local notation "fQCoh" => i𝒳 ⋙ fStar ⋙ Q𝒴
/-- The arrow `c`. -/
local notation "cupC" =>
  FibredSite.directImageNaiveCupProduct B S hS 𝒳.val.val.p 𝒴.val.val.p 𝒳.val.isFiberedInGroupoids
    𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism f.hom.hom.w)

/-- **The left vertical arrow of Stacks 0GQR**,
`f_{QCoh,*}𝓕 ⊗ f_{QCoh,*}𝓖 ⟶ f_{QCoh,*}(𝓕 ⊗ 𝓖)`, for a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic
stacks: `Q(c)` precomposed with the comparison `Q(A) ⊗ Q(B) ⟶ Q(A ⊗ B)` of Remark 0GQM
(`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentCupProduct_eq`). Here
`f_{QCoh,*} = Q ∘ f_* ∘ i`, with `f_*` the direct image of the morphism of ringed topoi `f`
induces and `Q` the coherator `AlgebraicGeometry.Stack.AlgebraicStacks.coherator` of `𝒴`. -/
@[stacks 0GQR "the left vertical arrow, Q applied to c through the comparison of Remark 0GQM"]
def quasicoherentCupProduct (𝓕 𝓖 : quasicoherentModules B S hS 𝒳) :
    (tensorQ𝒴).obj ((Q𝒴).obj ((fStar).obj ((i𝒳).obj 𝓕)), (Q𝒴).obj ((fStar).obj ((i𝒳).obj 𝓖))) ⟶
      (Q𝒴).obj ((fStar).obj ((i𝒳).obj ((tensorQ𝒳).obj (𝓕, 𝓖)))) :=
  Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct adjQ tensorQ𝒴 tensor𝒴
    (tensorIso𝒴).hom (cupC 𝓕 𝓖)

section Comparison

attribute [local instance] FlatFppf.hasSheafify_fppf_addCommGrpCat
  FlatFppf.wEqualsLocallyBijective_fppf_addCommGrpCat FlatFppf.hasSheafify_associatedTopology_ab
  FlatFppf.wEqualsLocallyBijective_fppfTopology_addCommGrpCat

/-- **The left vertical arrow is `Q(c)` after the comparison of Remark 0GQM.** The comparison is
the multiplication `μ` of the lax monoidal structure that the coherator receives as the right
adjoint of the symmetric monoidal inclusion `QCoh(𝒪_𝒴) ⊆ Mod(𝒪_𝒴)`
(`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentInclusionBraided`, **Stacks 0GQM** (iii)),
for the monoidal structure `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` of
Tag 01CA; it is the map shown invertible on `LQCoh^fbc(𝒪_𝒴)` by **Stacks 0GQM** (iv)
(`AlgebraicGeometry.Stack.AlgebraicStacks.isIso_coheratorTensorComparison`). -/
theorem quasicoherentCupProduct_eq (𝓕 𝓖 : quasicoherentModules B S hS 𝒳) :
    letI := fppfModulesMonoidal B S hS 𝒴
    letI := quasicoherentInclusionBraided B S hS 𝒴
    letI := (adjQ).rightAdjointLaxMonoidal
    quasicoherentCupProduct B S hS f 𝓕 𝓖 =
      Functor.LaxMonoidal.μ (Q𝒴) ((fStar).obj ((i𝒳).obj 𝓕)) ((fStar).obj ((i𝒳).obj 𝓖)) ≫
        (Q𝒴).map (cupC 𝓕 𝓖) := by
  let := fppfModulesMonoidal B S hS 𝒴
  let := quasicoherentInclusionBraided B S hS 𝒴
  let := (adjQ).rightAdjointLaxMonoidal
  unfold quasicoherentCupProduct Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct
  rw [Adjunction.rightAdjointLaxMonoidal_μ]
  unfold Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct
  congr 2
  simp only [FibredSite.quasicoherentSheafTensorCompInclusionIso, ObjectProperty.liftCompιIso,
    Iso.refl_hom, NatTrans.id_app, ObjectProperty.ι_δ, Category.id_comp]
  exact (Category.id_comp _).trans
    (Stacks.SheafOfModules.Strict.tensorHom_eq_tensorSheafBifunctor_map
      (FlatFppf.fppfRingedTopos B S hS 𝒴).O _ _).symm

end Comparison

/-- **Stacks 0GQR.** Let `f : 𝒳 ⟶ 𝒴` be a quasi-compact and quasi-separated 1-morphism of
algebraic stacks and let `𝓕`, `𝓖` be quasi-coherent `𝒪_𝒳`-modules. The square

```
f_{QCoh,*}𝓕 ⊗ f_{QCoh,*}𝓖 ───→ f_*𝓕 ⊗ f_*𝓖
        │                              │ c
        ↓                              ↓
f_{QCoh,*}(𝓕 ⊗ 𝓖) ─────────→ f_*(𝓕 ⊗ 𝓖)
```

commutes: the left vertical arrow
(`AlgebraicGeometry.Stack.AlgebraicStacks.quasicoherentCupProduct`, the comparison of
Remark 0GQM followed by `Q(c)`) followed by the counit `Q ⟶ id` at `f_*(𝓕 ⊗ 𝓖)` equals the top
arrow (`i` commuting with `⊗`, then the counit at `f_*𝓕` and at `f_*𝓖`) followed by the naive
relative cup product `c` (`AlgebraicGeometry.FibredSite.directImageNaiveCupProduct`). `f_*` is
the direct image along the morphism of ringed topoi `f` induces, and `Q` is the coherator
`AlgebraicGeometry.Stack.AlgebraicStacks.coherator` of `𝒴`, which takes no input. -/
@[stacks 0GQR "commutativity of the diagram, for a quasi-compact quasi-separated 1-morphism of \
algebraic stacks"]
theorem map_quasicoherentCupProduct_comp_counit
    (_hqc : IsQuasiCompactMorphism B S hS f) (_hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (𝓕 𝓖 : quasicoherentModules B S hS 𝒳) :
    (i𝒴).map (quasicoherentCupProduct B S hS f 𝓕 𝓖) ≫
        (adjQ).counit.app ((fStar).obj ((i𝒳).obj ((tensorQ𝒳).obj (𝓕, 𝓖)))) =
      (tensorIso𝒴).hom.app ((Q𝒴).obj ((fStar).obj ((i𝒳).obj 𝓕)),
          (Q𝒴).obj ((fStar).obj ((i𝒳).obj 𝓖))) ≫
        (tensor𝒴).map ((adjQ).counit.app ((fStar).obj ((i𝒳).obj 𝓕)) ×ₘ
          (adjQ).counit.app ((fStar).obj ((i𝒳).obj 𝓖))) ≫
        cupC 𝓕 𝓖 := by
  unfold quasicoherentCupProduct
  rw [Stacks.Cohomology.DegreeZeroCupProduct.map_coheratorCupProduct_comp_counit adjQ
    tensorQ𝒴 tensor𝒴 (tensorIso𝒴).hom (cupC 𝓕 𝓖)]

/-- **Stacks 0GQR, functoriality of the left vertical arrow** in `𝓕` and `𝓖`, for a
quasi-compact quasi-separated 1-morphism of algebraic stacks. -/
@[stacks 0GQR "the construction is functorial in F and G: the left vertical arrow"]
theorem quasicoherentCupProduct_natural
    (_hqc : IsQuasiCompactMorphism B S hS f) (_hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    {𝓕 𝓕' 𝓖 𝓖' : quasicoherentModules B S hS 𝒳} (a : 𝓕 ⟶ 𝓕') (b : 𝓖 ⟶ 𝓖') :
    (tensorQ𝒴).map ((fQCoh).map a ×ₘ (fQCoh).map b) ≫ quasicoherentCupProduct B S hS f 𝓕' 𝓖' =
      quasicoherentCupProduct B S hS f 𝓕 𝓖 ≫ (fQCoh).map ((tensorQ𝒳).map (a ×ₘ b)) :=
  Stacks.Cohomology.DegreeZeroCupProduct.coheratorCupProduct_natural adjQ tensorQ𝒴 tensor𝒴
    (tensorIso𝒴).hom ((fStar).map ((i𝒳).map a)) ((fStar).map ((i𝒳).map b)) (cupC 𝓕 𝓖)
    (cupC 𝓕' 𝓖') ((fStar).map ((i𝒳).map ((tensorQ𝒳).map (a ×ₘ b))))
    (FibredSite.directImageNaiveCupProduct_natural B S hS 𝒳.val.val.p 𝒴.val.val.p
      𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
      (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism f.hom.hom.w) a b)

/-- **Stacks 0GQR, functoriality of the naive relative cup product `c`** in `𝓕` and `𝓖`, for a
quasi-compact quasi-separated 1-morphism of algebraic stacks. -/
@[stacks 0GQR "the construction is functorial in F and G: the arrow c"]
theorem quasicoherentNaiveCupProduct_natural
    (_hqc : IsQuasiCompactMorphism B S hS f) (_hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    {𝓕 𝓕' 𝓖 𝓖' : quasicoherentModules B S hS 𝒳} (a : 𝓕 ⟶ 𝓕') (b : 𝓖 ⟶ 𝓖') :
    (tensor𝒴).map ((fStar).map ((i𝒳).map a) ×ₘ (fStar).map ((i𝒳).map b)) ≫ cupC 𝓕' 𝓖' =
      cupC 𝓕 𝓖 ≫ (fStar).map ((i𝒳).map ((tensorQ𝒳).map (a ×ₘ b))) :=
  FibredSite.directImageNaiveCupProduct_natural B S hS 𝒳.val.val.p 𝒴.val.val.p
    𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids f.hom.hom.toFunctor
    (𝒴.val.isFiberedInGroupoids.isFibredOneMorphism f.hom.hom.w) a b

end AlgebraicGeometry.Stack.AlgebraicStacks

end
