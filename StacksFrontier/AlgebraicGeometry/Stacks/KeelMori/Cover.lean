module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.EtaleModuliSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleStabilizerPreservingIsomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationEquivalenceInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.ParasiticLisseEtaleVanishing

/-!
# Étale covers of an algebraic stack by well-nigh affine stacks (setup of Stacks 0DUT)

The proof of the Keel–Mori theorem (Stacks 0DUT) starts from a family of 1-morphisms
`g i : 𝒳 i ⟶ 𝒳` as produced by Stacks 0DUE: jointly surjective on points, with well-nigh affine
sources, representable by algebraic spaces, separated, étale, and inducing isomorphisms on
automorphism groups. This file packages such a family as
`AlgebraicGeometry.Stack.KeelMoriCover`, fixes for each `i` the moduli space `f i : 𝒳 i ⟶ M i`
of a chosen chart (Stacks 0DUP), and constructs, for each pair `(i, j)`, the first part of the
data of the proof: with `𝒳 i j = 𝒳 i ×_𝒳 𝒳 j`, a separated étale morphism of schemes
`s i j : N i j ⟶ M i` and a 1-morphism `φ i j : 𝒳 i j ⟶ N i j` making
```
𝒳 i j ⟶ 𝒳 i
  ↓        ↓ f i
N i j ⟶ M i
```
2-cartesian (Stacks 0DUS), and a separated étale `t i j : N i j ⟶ M j` with
`φ i j ≫ t i j = pr₂ ≫ f j`.

## Main definitions

* `AlgebraicGeometry.Stack.KeelMoriCover`
* `AlgebraicGeometry.Stack.KeelMoriCover.M`, `.f`: the chosen moduli spaces.
* `AlgebraicGeometry.Stack.KeelMoriCover.N`, `.φ`, `.s`, `.t`: the data attached to a pair.

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.isUniformCategoricalModuliSpace_f`
* `AlgebraicGeometry.Stack.KeelMoriCover.isTwoFibreProduct_square`
* `AlgebraicGeometry.Stack.KeelMoriCover.isUniformCategoricalModuliSpace_φ`
* `AlgebraicGeometry.Stack.KeelMoriCover.φ_comp_t`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An étale cover of an algebraic stack by well-nigh affine algebraic stacks** with all the
properties listed in Stacks 0DUE: a family of 1-morphisms `map i : obj i ⟶ 𝒳`, indexed by a type
of the working universe, jointly surjective on points, with well-nigh affine sources (with a
chosen chart), inducing isomorphisms on automorphism groups at every point, representable by
algebraic spaces, separated and étale. -/
structure KeelMoriCover (𝒳 : AlgebraicStacks.{u, w} B S hS) where
  /-- The index type. -/
  ι : Type u
  /-- The members of the cover. -/
  obj : ι → AlgebraicStacks.{u, w} B S hS
  /-- The 1-morphisms of the cover. -/
  map : ∀ i, obj i ⟶ 𝒳
  /-- The members are well-nigh affine. -/
  wellNighAffine : ∀ i, IsWellNighAffine.{u, w} B S hS (obj i)
  /-- A chosen chart of each member. -/
  chart : ∀ i, WellNighAffineChart.{u, w} B S hS (obj i)
  /-- The family is jointly surjective on points. -/
  cover : ∀ x : points B S hS 𝒳.val.val 𝒳.val.isFiberedInGroupoids,
    ∃ (i : ι) (y : points B S hS (obj i).val.val (obj i).val.isFiberedInGroupoids),
      pointsMap B S hS (obj i).val.val (obj i).val.isFiberedInGroupoids
        𝒳.val.isFiberedInGroupoids (map i).hom.hom y = x
  /-- The members induce isomorphisms on automorphism groups at every point. -/
  inducesIso : ∀ i (q : points B S hS (obj i).val.val (obj i).val.isFiberedInGroupoids),
    InducesIsomorphismAt B S hS (map i) q
  /-- The members are representable by algebraic spaces. -/
  rep : ∀ i, IsRepresentableByAlgebraicSpaces B S hS (map i).hom.hom
  /-- The members are separated. -/
  separated : ∀ i, AlgebraicStacks.IsSeparated B S hS (map i)
  /-- The members are étale. -/
  etale : ∀ i, IsEtale B S hS (map i)

namespace KeelMoriCover

variable {B S hS} {𝒳 : AlgebraicStacks.{u, w} B S hS} (C : KeelMoriCover B S hS 𝒳)

/-! ### The moduli space of each member -/

/-- The moduli space of the `i`-th member, an affine object of the site (Stacks 0DUP). -/
noncomputable abbrev M (i : C.ι) : BigFppfOver B S hS := (C.chart i).moduliObject

/-- The algebraic space of the moduli space of the `i`-th member. -/
noncomputable abbrev Msp (i : C.ι) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (C.M i), isAlgebraicSpace_yoneda B S hS (C.M i)⟩

/-- The moduli morphism of the `i`-th member (Stacks 0DUP). -/
noncomputable abbrev f (i : C.ι) :
    C.obj i ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj (C.M i))
      (isAlgebraicSpace_yoneda B S hS (C.M i)) :=
  (C.chart i).moduliMap

/-- **The moduli morphism of each member is a uniform categorical moduli space** (Stacks 0DUP and
Stacks 0DUR). -/
theorem isUniformCategoricalModuliSpace_f (i : C.ι) :
    IsUniformCategoricalModuliSpace B S hS (C.Msp i) (C.f i).hom :=
  isUniformCategoricalModuliSpace_of_isUniformCategoricalModuliSpaceIn B S hS _
    (C.wellNighAffine i) _ _ (C.chart i).isUniformCategoricalModuliSpaceIn_moduliMap

/-- The moduli morphism `f i` of each member is a categorical moduli space. -/
theorem isCategoricalModuliSpace_f (i : C.ι) :
    IsCategoricalModuliSpace B S hS (C.Msp i) (C.f i).hom :=
  isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS
    (C.isUniformCategoricalModuliSpace_f i)

/-! ### The fibre product of two members -/

/-- The canonical 2-fibre product square of the `i`-th and `j`-th members over `𝒳`. -/
noncomputable abbrev pairSq (i j : C.ι) : Bicategory.TwoCommSq (C.map i) (C.map j) :=
  twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map j)

/-- The 2-fibre product `𝒳 i ×_𝒳 𝒳 j`. -/
noncomputable abbrev X (i j : C.ι) : AlgebraicStacks.{u, w} B S hS := (C.pairSq i j).pt

/-- The first projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 i`. -/
noncomputable abbrev pr₁ (i j : C.ι) : C.X i j ⟶ C.obj i := (C.pairSq i j).fst

/-- The second projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j`. -/
noncomputable abbrev pr₂ (i j : C.ι) : C.X i j ⟶ C.obj j := (C.pairSq i j).snd

/-- The first projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 i` is relatively étale. -/
theorem isRelativelyEtale_pr₁ (i j : C.ι) : IsRelativelyEtale B S hS (C.pr₁ i j).hom :=
  isRelativelyEtale_baseChange B S hS _ _ _ (C.map j).hom (C.map i).hom
    (C.pairSq i j).underlying
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (C.map i).hom (C.map j).hom)
    (isRelativelyEtale_of_isEtale B S hS (C.map j) (C.rep j) (C.etale j))

/-- The first projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 i` is étale. -/
theorem isEtale_pr₁ (i j : C.ι) : IsEtale B S hS (C.pr₁ i j) :=
  AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS (C.pr₁ i j) (C.isRelativelyEtale_pr₁ i j)

/-- The first projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 i` is separated. -/
theorem isSeparated_pr₁ (i j : C.ι) : AlgebraicStacks.IsSeparated B S hS (C.pr₁ i j) :=
  AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct B S hS (C.map j) (C.map i)
    (C.pairSq i j).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map j)))
    (C.separated j)

/-- The first projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 i` induces isomorphisms on automorphism groups at
every point. -/
theorem inducesIsomorphismAt_pr₁ (i j : C.ι)
    (q : points B S hS (C.X i j).val.val (C.X i j).val.isFiberedInGroupoids) :
    InducesIsomorphismAt B S hS (C.pr₁ i j) q :=
  inducesIsomorphismAt_baseChange B S hS (C.map j) (C.map i) (C.pairSq i j)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map j)) q
    (C.inducesIso j _)

/-- The second projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j` is relatively étale. -/
theorem isRelativelyEtale_pr₂ (i j : C.ι) : IsRelativelyEtale B S hS (C.pr₂ i j).hom :=
  isRelativelyEtale_baseChange B S hS _ _ _ (C.map i).hom (C.map j).hom
    (C.pairSq i j).underlying.swap
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        (C.map i).hom (C.map j).hom))
    (isRelativelyEtale_of_isEtale B S hS (C.map i) (C.rep i) (C.etale i))

/-- The second projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j` is étale. -/
theorem isEtale_pr₂ (i j : C.ι) : IsEtale B S hS (C.pr₂ i j) :=
  AlgebraicStacks.isEtale_of_isRelativelyEtale B S hS (C.pr₂ i j) (C.isRelativelyEtale_pr₂ i j)

/-- The second projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j` is separated. -/
theorem isSeparated_pr₂ (i j : C.ι) : AlgebraicStacks.IsSeparated B S hS (C.pr₂ i j) :=
  AlgebraicStacks.isSeparated_baseChange_of_isTwoFibreProduct B S hS (C.map i) (C.map j)
    (C.pairSq i j)
    (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map j))
    (C.separated i)

/-- The second projection `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j` induces isomorphisms on automorphism groups at
every point. -/
theorem inducesIsomorphismAt_pr₂ (i j : C.ι)
    (q : points B S hS (C.X i j).val.val (C.X i j).val.isFiberedInGroupoids) :
    InducesIsomorphismAt B S hS (C.pr₂ i j) q :=
  inducesIsomorphismAt_baseChange B S hS (C.map i) (C.map j) (C.pairSq i j).swap
    (Bicategory.isTwoFibreProduct_swap
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS (C.map i) (C.map j))) q
    (C.inducesIso i _)

/-! ### The moduli square of a pair -/

/-- There are an object `M'`, a 1-morphism `f' : 𝒳 i ×_𝒳 𝒳 j ⟶ M'` and a separated étale
morphism `g : M' ⟶ M i` with `f' ≫ g = pr₁ ≫ f i`, such that the resulting square is
2-cartesian. -/
theorem exists_square (i j : C.ι) :
    ∃ (M' : BigFppfOver B S hS)
      (f' : C.X i j ⟶
        algebraicSpaceStack.{u, w} B S hS (yoneda.obj M') (isAlgebraicSpace_yoneda B S hS M'))
      (g : M' ⟶ C.M i)
      (hcomm : f'.hom ≫ (associatedMap B S hS (yoneda.map g)).1 = (C.pr₁ i j).hom ≫ (C.f i).hom),
      Etale ((BigFppfOver.toScheme B S hS).map g) ∧
      _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map g) ∧
      Nonempty (Bicategory.IsTwoFibreProduct
        (ChartBaseChange.moduliSquare (C.pr₁ i j) g (C.f i).hom f'.hom hcomm)) :=
  exists_moduliSquare_of_isEtale_of_isSeparated B S hS (C.pr₁ i j) (C.wellNighAffine i)
    (C.isEtale_pr₁ i j) (C.isSeparated_pr₁ i j) (C.inducesIsomorphismAt_pr₁ i j) (C.M i) (C.f i)
    (C.isCategoricalModuliSpace_f i)

/-- The scheme `N i j` of the moduli square of the pair `(i, j)`. -/
noncomputable def N (i j : C.ι) : BigFppfOver B S hS := (C.exists_square i j).choose

/-- The algebraic space of `N i j`. -/
noncomputable abbrev Nsp (i j : C.ι) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (C.N i j), isAlgebraicSpace_yoneda B S hS (C.N i j)⟩

/-- The moduli morphism `φ i j : 𝒳 i ×_𝒳 𝒳 j ⟶ N i j`. -/
noncomputable def φ (i j : C.ι) :
    C.X i j ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj (C.N i j))
      (isAlgebraicSpace_yoneda B S hS (C.N i j)) :=
  (C.exists_square i j).choose_spec.choose

/-- The separated étale morphism `s i j : N i j ⟶ M i`. -/
noncomputable def s (i j : C.ι) : C.N i j ⟶ C.M i :=
  (C.exists_square i j).choose_spec.choose_spec.choose

/-- The moduli square of a pair commutes: `φ i j ≫ s i j = pr₁ i j ≫ f i`. -/
theorem φ_comp_s (i j : C.ι) :
    (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map (C.s i j))).1 =
      (C.pr₁ i j).hom ≫ (C.f i).hom :=
  (C.exists_square i j).choose_spec.choose_spec.choose_spec.choose

/-- The morphism of schemes underlying `s i j` is étale. -/
instance etale_s (i j : C.ι) : Etale ((BigFppfOver.toScheme B S hS).map (C.s i j)) :=
  (C.exists_square i j).choose_spec.choose_spec.choose_spec.choose_spec.1

/-- The morphism of schemes underlying `s i j` is separated. -/
instance isSeparated_s (i j : C.ι) :
    _root_.AlgebraicGeometry.IsSeparated ((BigFppfOver.toScheme B S hS).map (C.s i j)) :=
  (C.exists_square i j).choose_spec.choose_spec.choose_spec.choose_spec.2.1

/-- **The moduli square of a pair is 2-cartesian**: `𝒳 i ×_𝒳 𝒳 j = N i j ×_{M i} 𝒳 i`. -/
noncomputable def isTwoFibreProduct_square (i j : C.ι) :
    Bicategory.IsTwoFibreProduct
      (ChartBaseChange.moduliSquare (C.pr₁ i j) (C.s i j) (C.f i).hom (C.φ i j).hom
        (C.φ_comp_s i j)) :=
  (C.exists_square i j).choose_spec.choose_spec.choose_spec.choose_spec.2.2.some

/-- The morphism of algebraic spaces attached to `s i j`. -/
noncomputable abbrev sSp (i j : C.ι) : C.Nsp i j ⟶ C.Msp i :=
  ObjectProperty.homMk (yoneda.map (C.s i j))

/-- The morphism of algebraic spaces `sSp i j : N i j ⟶ M i` is flat. -/
theorem isFlat_sSp (i j : C.ι) : Space.IsFlat B S hS (C.sSp i j).hom :=
  (isFlat_yoneda_map_iff B S hS (C.s i j)).2 inferInstance

/-- **The moduli morphism of a pair is a uniform categorical moduli space**: it is a flat base
change of the uniform categorical moduli space `f i`. -/
theorem isUniformCategoricalModuliSpace_φ (i j : C.ι) :
    IsUniformCategoricalModuliSpace B S hS (C.Nsp i j) (C.φ i j).hom :=
  isUniformCategoricalModuliSpace_fst B S hS (C.isUniformCategoricalModuliSpace_f i)
    (C.sSp i j) (C.isFlat_sSp i j) _ (C.isTwoFibreProduct_square i j)

/-- The moduli morphism `φ i j` of a pair is a categorical moduli space. -/
theorem isCategoricalModuliSpace_φ (i j : C.ι) :
    IsCategoricalModuliSpace B S hS (C.Nsp i j) (C.φ i j).hom :=
  isCategoricalModuliSpace_of_isUniformCategoricalModuliSpace B S hS
    (C.isUniformCategoricalModuliSpace_φ i j)

/-! ### The second morphism of a pair -/

/-- There is a morphism `t : N i j ⟶ M j` with `φ i j ≫ t = pr₂ i j ≫ f j`. -/
theorem exists_t (i j : C.ι) :
    ∃ t : C.N i j ⟶ C.M j,
      (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map t)).1 = (C.pr₂ i j).hom ≫ (C.f j).hom := by
  obtain ⟨h, ⟨η⟩, -⟩ := C.isCategoricalModuliSpace_φ i j (C.Msp j) ((C.pr₂ i j).hom ≫ (C.f j).hom)
  exact ⟨Yoneda.fullyFaithful.preimage h.hom, by
    rw [Yoneda.fullyFaithful.map_preimage]; exact hom_eq_of_hom₂ B S hS η.hom⟩

/-- The morphism `t i j : N i j ⟶ M j`, the factorization of `𝒳 i ×_𝒳 𝒳 j ⟶ 𝒳 j ⟶ M j` through
the moduli morphism of the pair. -/
noncomputable def t (i j : C.ι) : C.N i j ⟶ C.M j := (C.exists_t i j).choose

/-- The morphism `t i j` satisfies `φ i j ≫ t i j = pr₂ i j ≫ f j`. -/
theorem φ_comp_t (i j : C.ι) :
    (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map (C.t i j))).1 =
      (C.pr₂ i j).hom ≫ (C.f j).hom :=
  (C.exists_t i j).choose_spec

/-- Two morphisms out of the moduli space `P` of a 1-morphism `F` factoring the same 1-morphism
are equal. -/
private theorem hom_ext_of_isCategoricalModuliSpace {𝒴 : AlgebraicStacks.{u, w} B S hS}
    {P Y : BigFppfOver B S hS}
    (F : 𝒴 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj P) (isAlgebraicSpace_yoneda B S hS P))
    (hF : IsCategoricalModuliSpace B S hS ⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩ F.hom)
    (a b : P ⟶ Y)
    (h : F.hom ≫ (associatedMap B S hS (yoneda.map a)).1 =
      F.hom ≫ (associatedMap B S hS (yoneda.map b)).1) : a = b := by
  have := eq_of_isCategoricalModuliSpace B S hS hF
    (F.hom ≫ (associatedMap B S hS (yoneda.map b)).1)
    (ObjectProperty.homMk (yoneda.map a) :
      (⟨yoneda.obj P, isAlgebraicSpace_yoneda B S hS P⟩ : AlgebraicSpaces B S hS) ⟶
        ⟨yoneda.obj Y, isAlgebraicSpace_yoneda B S hS Y⟩)
    (ObjectProperty.homMk (yoneda.map b)) ⟨eqToIso (by exact h)⟩ ⟨Iso.refl _⟩
  exact yoneda.map_injective (congrArg (fun k => k.hom) this)

/-- **Two morphisms out of `N i j` factoring the same 1-morphism are equal.** -/
theorem hom_ext_N {i j : C.ι} {Y : BigFppfOver B S hS} (a b : C.N i j ⟶ Y)
    (h : (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map a)).1 =
      (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map b)).1) : a = b :=
  hom_ext_of_isCategoricalModuliSpace (C.φ i j) (C.isCategoricalModuliSpace_φ i j) a b h

/-- **Two morphisms out of `M i` factoring the same 1-morphism are equal.** -/
theorem hom_ext_M {i : C.ι} {Y : BigFppfOver B S hS} (a b : C.M i ⟶ Y)
    (h : (C.f i).hom ≫ (associatedMap B S hS (yoneda.map a)).1 =
      (C.f i).hom ≫ (associatedMap B S hS (yoneda.map b)).1) : a = b :=
  hom_ext_of_isCategoricalModuliSpace (C.f i) (C.isCategoricalModuliSpace_f i) a b h

end KeelMoriCover

end AlgebraicGeometry.Stack

end
