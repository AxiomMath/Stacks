module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushPullComposition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushPullIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardForget

/-!
# Derived pushforward commutes with restriction of scalars

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed sites, presented as a continuous
functor `uf : C' ⥤ C` in the direction opposite to `f` together with the structure map
`σ : O' ⟶ f_*O`. Let `A` be a sheaf of differential graded `O`-algebras, `B` one of
`O'`-algebras and `φ : B ⟶ f_*A` a homomorphism. Let moreover `Z` be a sheaf of differential
graded `O`-algebras with `ιA : Z ⟶ A` over the *identity* morphism of the ringed site
`(Sh(C), O)`, let `W` be one of `O'`-algebras with `ιB : W ⟶ B` over the identity morphism of
`(Sh(C'), O')`, and let `χ : W ⟶ f_*Z`, the four homomorphisms making a commuting square
`φ ∘ ιB = f_*(ιA) ∘ χ` of homomorphisms `W ⟶ f_*A`. Then the square

`Rf_* ⋙ R(id_{C'})_* ≅ R(id_C)_* ⋙ Rχ_* : D(A, d) ⥤ D(W, d)`

commutes. This is a variant of [Stacks, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW) for
an exact direct image: the two horizontal arrows are derived restrictions of scalars and the two
vertical arrows are the derived pushforwards along `f`. Tag 0FTW itself, with the forgetful
functors to the derived categories of sheaves of modules and the derived pushforwards for an
arbitrary morphism of ringed topoi, is
`SheafOfModules.DifferentialGradedModule.derivedToposPushforwardForgetIso`.

The source's own proof is followed. The restriction of scalars along a homomorphism of sheaves
of differential graded algebras over the identity morphism of ringed topoi — the pushforward
`id_{C,*}` of [Stacks, Tag 0FRT](https://stacks.math.columbia.edu/tag/0FRT) — leaves the
underlying complex of sheaves of modules unchanged, so it is exact and `R id_{C,*}` is the
functor it induces on the derived categories, which under the source's identification
`Mod(O, 0) = Comp(O)` is the forgetful functor. The square of direct images
`ιB_* ∘ f_*^φ = χ_* ∘ ιA_*` holds already on differential graded modules, because both are the
direct image attached to the one composite homomorphism `W ⟶ f_*A`. Both composites of the
square therefore factor the same functor `K(A, d) ⥤ D(W, d)` through the localization
`K(A, d) ⥤ D(A, d)`, and the conclusion is uniqueness of such a factorisation. No calculus of
fractions, no adjunction, no derived pullback and no comparison between derived functors is
used.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedPushforwardRestrictionSquareIso` is the
  isomorphism `Rf_* ⋙ R(id_{C'})_* ≅ R(id_C)_* ⋙ Rχ_*` of the square.
* `SheafOfModules.DifferentialGradedModule.pullbackFunctorSquareIso` is the module-level square
  `ιB^* ⋙ φ^* ≅ χ^* ⋙ ιA^*` of pullbacks of differential graded modules, built from the
  commuting square of homomorphisms of algebras.
* `SheafOfModules.DifferentialGradedModule.homotopyPullbackFunctorSquareIso` is
  `K(ιB^*) ⋙ K(φ^*) ≅ K(χ^*) ⋙ K(ιA^*)`, a module-level square of pullbacks descended to the
  homotopy categories.
* `SheafOfModules.DifferentialGradedModule.derivedPullbackOfInvertsSquareIso` is
  `LιB^* ⋙ Lφ^* ≅ Lχ^* ⋙ LιA^*`, the same square for the derived pullbacks of exact pairs.

## Main results

* `SheafOfModules.DifferentialGradedModule.homotopyPushforwardFunctor_square`: the square of
  direct images on the homotopy categories, an equality of functors.
* `SheafOfModules.DifferentialGradedModule.nonempty_derivedPushforward_restriction_square_iso`:
  the square of derived pushforwards commutes.

## Implementation notes

**What the hypotheses are.** Beyond the source's data the statement asks one thing of the
morphism: that its direct image of sheaves of modules preserve homology. That makes `K(f_*)`
invert the quasi-isomorphisms for both of the two homomorphisms over `f`, so that both derived
pushforwards along `f` are the functors induced on the derived categories. For a morphism whose
direct image is merely left exact the derived pushforward is a right derived extension, which
this development does not build: the homotopy category of sheaves of differential graded modules
carries no triangulated structure here, so the existence of the extension is out of reach. The
two restrictions of scalars need no such hypothesis, being exact for every `ιA` and `ιB`.

**Why `Z` and `W` are arbitrary.** The source takes `Z = (O_C, 0)` and `W = (O_D, 0)`, the
differential graded algebras with the structure sheaf in degree zero and the zero differential,
and identifies `Mod(O, 0)` with `Comp(O)`; that identification is absent from this development,
so the two restrictions of scalars are taken along arbitrary `ιA : Z ⟶ A` and `ιB : W ⟶ B` over
the identity morphisms of ringed sites. The commuting square `φ ∘ ιB = f_*(ιA) ∘ χ`, which in
the source holds because both composites are the unit map `(O_D, 0) ⟶ f_*A`, is part of the
data here. Its two sides have the same type on the nose: `𝟭 C' ⋙ uf` and `uf ⋙ 𝟭 C` are the
functor `uf`, and both composite structure maps are `σ`.

**The square of derived pullbacks.** The second half of the file records the same square for
the derived pullbacks of exact pairs, `LιB^* ⋙ Lφ^* ≅ Lχ^* ⋙ LιA^*`, from a module-level square
`ιB^* ⋙ φ^* ≅ χ^* ⋙ ιA^*` of pullbacks of differential graded modules; that module-level square
is itself built, by `pullbackFunctorSquareIso`, from the commuting square of homomorphisms of
algebras and the universality of the two inner units which already makes pullbacks compose. It
is the analogue for a square of
[Stacks, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI), and it is independent of the
pushforward statement above, which needs no pullback at all.

The universes of the two sites and of their morphisms and of the homogeneous pieces of the four
algebras are independent. The two sheaves of rings share a universe because the structure map
relates them, and the module sections share a universe because the direct image of sheaves of
modules preserves it.

## References

* [Stacks Project, Tag 0FTW](https://stacks.math.columbia.edu/tag/0FTW)
* [Stacks Project, Tag 0FRT](https://stacks.math.columbia.edu/tag/0FRT)
* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
-/

@[expose] public section

open CategoryTheory

universe t a a' b b' m v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {Z : DifferentialGradedAlgebra.{t, b} R} {W : DifferentialGradedAlgebra.{t, b'} R'}
  {uf : C' ⥤ C} [uf.IsContinuous J' J] {σ : R'.obj ⟶ uf.op ⋙ R.obj}

/-! ### The square of direct images and the square of derived pushforwards -/

section Pushforward

variable {φ : DifferentialGradedAlgebra.SemilinearHom uf σ B A}
  {ιA : DifferentialGradedAlgebra.SemilinearHom (𝟭 C) (𝟙 R.obj) Z A}
  {ιB : DifferentialGradedAlgebra.SemilinearHom (𝟭 C') (𝟙 R'.obj) W B}
  {χ : DifferentialGradedAlgebra.SemilinearHom uf σ W Z}

/-- **The square of direct images on the homotopy categories.** The direct image along `f`
followed by the restriction of scalars along `ιB` is the restriction of scalars along `ιA`
followed by the direct image along `f`, as an equality of functors
`K(Mod(A, d)) ⥤ K(Mod(W, d))`. Both sides are the direct image attached to the one composite
homomorphism `W ⟶ f_*A`, by `homotopyPushforwardFunctor_trans` and the commuting square. -/
theorem homotopyPushforwardFunctor_square
    (hsq : (ιB.trans φ : DifferentialGradedAlgebra.SemilinearHom uf σ W A) = χ.trans ιA) :
    (homotopyPushforwardFunctor φ :
          HomotopyCategory.{t, a, m} A ⥤ HomotopyCategory.{t, a', m} B) ⋙
        homotopyPushforwardFunctor ιB =
      homotopyPushforwardFunctor ιA ⋙ homotopyPushforwardFunctor χ := by
  have : (𝟭 C' ⋙ uf).IsContinuous J' J := inferInstanceAs (uf.IsContinuous J' J)
  have : (uf ⋙ 𝟭 C).IsContinuous J' J := inferInstanceAs (uf.IsContinuous J' J)
  rw [← homotopyPushforwardFunctor_trans, ← homotopyPushforwardFunctor_trans, hsq]
  rfl

variable (hex : (sitePushforward uf σ :
  SheafOfModules.{m} R ⥤ SheafOfModules.{m} R').PreservesHomology)

/-- **The square of derived pushforwards.** Both composites lift the direct image along the
composite homomorphism `W ⟶ f_*A`, followed by the localization, through the localization
`K(Mod(A, d)) ⥤ D(A, d)`: on the left through the two comparison isomorphisms of
`derivedPushforwardOfInverts`, on the right through those two and the square
`homotopyPushforwardFunctor_square`. A functor out of a localization is determined up to
isomorphism by what it lifts. -/
noncomputable def derivedPushforwardRestrictionSquareIso
    (hsq : (ιB.trans φ : DifferentialGradedAlgebra.SemilinearHom uf σ W A) = χ.trans ιA) :
    derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := φ) hex) ⋙
        derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιB) ≅
      derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιA) ⋙
        derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := χ) hex) := by
  letI : Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      ((homotopyPushforwardFunctor φ ⋙ homotopyPushforwardFunctor ιB) ⋙
        toDerivedCategory.{t, b', m} W)
      (derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := φ) hex) ⋙
        derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιB)) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComparisonIsoOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := φ) hex)).symm
        (derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιB)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homotopyPushforwardFunctor φ)
        (pushforwardComparisonIsoOfInverts
          (idIsInvertedBy_homotopyPushforwardFunctor_comp ιB)).symm ≪≫
      (Functor.associator _ _ _).symm⟩
  letI : Localization.Lifting (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
      ((homotopyPushforwardFunctor φ ⋙ homotopyPushforwardFunctor ιB) ⋙
        toDerivedCategory.{t, b', m} W)
      (derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιA) ⋙
        derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := χ) hex)) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pushforwardComparisonIsoOfInverts
          (idIsInvertedBy_homotopyPushforwardFunctor_comp ιA)).symm
        (derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := χ) hex)) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homotopyPushforwardFunctor ιA)
        (pushforwardComparisonIsoOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology
            (φ := χ) hex)).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso (homotopyPushforwardFunctor_square hsq).symm)
        (toDerivedCategory.{t, b', m} W)⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, a, m} A) (quasiIsomorphisms.{t, a, m} A)
    ((homotopyPushforwardFunctor φ ⋙ homotopyPushforwardFunctor ιB) ⋙
      toDerivedCategory.{t, b', m} W)
    ((homotopyPushforwardFunctor φ ⋙ homotopyPushforwardFunctor ιB) ⋙
      toDerivedCategory.{t, b', m} W)
    (derivedPushforwardOfInverts
        (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := φ) hex) ⋙
      derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιB))
    (derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιA) ⋙
      derivedPushforwardOfInverts
        (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := χ) hex))
    (Iso.refl _)

/-- **The square of derived pushforwards for an exact direct image.** Let
`(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of
ringed topoi, let `A` be a sheaf of differential graded `O_C`-algebras, `B` one of
`O_D`-algebras and `φ : B ⟶ f_*A` a homomorphism. Let `ιA : Z ⟶ A` and `ιB : W ⟶ B` be
homomorphisms of sheaves of differential graded algebras over the identity morphisms of the two
ringed topoi and let `χ : W ⟶ f_*Z` complete them to a commuting square of homomorphisms
`W ⟶ f_*A`. Then the derived pushforward along `f` followed by the derived restriction of
scalars along `ιB` is isomorphic to the derived restriction of scalars along `ιA` followed by
the derived pushforward along `f`: the square of the source commutes. -/
theorem nonempty_derivedPushforward_restriction_square_iso
    (hsq : (ιB.trans φ : DifferentialGradedAlgebra.SemilinearHom uf σ W A) = χ.trans ιA) :
    Nonempty (derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := φ) hex) ⋙
        derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιB) ≅
      derivedPushforwardOfInverts (idIsInvertedBy_homotopyPushforwardFunctor_comp ιA) ⋙
        derivedPushforwardOfInverts
          (isInvertedBy_homotopyPushforwardFunctor_comp_of_preservesHomology (φ := χ) hex)) :=
  ⟨derivedPushforwardRestrictionSquareIso hex hsq⟩

end Pushforward

/-! ### The square of pullbacks of differential graded modules -/

section ModulePullbackSquare

variable {φ : DifferentialGradedAlgebra.SemilinearHom uf σ B A}
  {ιA : DifferentialGradedAlgebra.SemilinearHom (𝟭 C) (𝟙 R.obj) Z A}
  {ιB : DifferentialGradedAlgebra.SemilinearHom (𝟭 C') (𝟙 R'.obj) W B}
  {χ : DifferentialGradedAlgebra.SemilinearHom uf σ W Z}
  (Pφ : PullbackData.{t, a, m, v, u, a', m} φ)
  (PA : PullbackData.{t, a, m, v, u, b, m} ιA)
  (PB : PullbackData.{t, a', m, v', u', b', m} ιB)
  (Pχ : PullbackData.{t, b, m, v, u, b', m} χ)

/-- **The square of pullbacks of differential graded modules**: `ιB^* ⋙ φ^* ≅ χ^* ⋙ ιA^*`.
Both composites are pullbacks along the one composite homomorphism `W ⟶ f_*A` — that is what
`PullbackData.trans` says, given that each inner unit stays universal for the outer morphism —
and a pullback is unique up to the canonical isomorphism compatible with the units,
`PullbackData.isoFunctor`. The commuting square `φ ∘ ιB = f_*(ιA) ∘ χ` of homomorphisms is what
makes the two composite homomorphisms the same one; its two sides have the same type on the
nose, `𝟭 C' ⋙ uf` and `uf ⋙ 𝟭 C` being `uf` and both composite structure maps being `σ`. -/
noncomputable def pullbackFunctorSquareIso
    (hB : ∀ (M : DifferentialGradedModule.{t, b', m} W)
      (N : DifferentialGradedModule.{t, a, m} A), (PB.unit M).IsUniversal φ N)
    (hχ : ∀ (M : DifferentialGradedModule.{t, b', m} W)
      (N : DifferentialGradedModule.{t, a, m} A), (Pχ.unit M).IsUniversal ιA N)
    (hsq : (ιB.trans φ : DifferentialGradedAlgebra.SemilinearHom uf σ W A) = χ.trans ιA) :
    PB.functor ⋙ Pφ.functor ≅ Pχ.functor ⋙ PA.functor :=
  Pφ.transIso PB (Pφ.trans PB hB) hB ≪≫
    eqToIso (PullbackData.functor_congr hsq (Pφ.trans PB hB)).symm ≪≫
    PullbackData.isoFunctor _ (PA.trans Pχ hχ) ≪≫
    (PA.transIso Pχ (PA.trans Pχ hχ) hχ).symm

end ModulePullbackSquare

/-! ### The square of derived pullbacks -/

section Pullback

variable {σA : R.obj ⟶ (𝟭 C).op ⋙ R.obj} {σB : R'.obj ⟶ (𝟭 C').op ⋙ R'.obj}
  {φ : DifferentialGradedAlgebra.SemilinearHom uf σ B A}
  {ιA : DifferentialGradedAlgebra.SemilinearHom (𝟭 C) σA Z A}
  {ιB : DifferentialGradedAlgebra.SemilinearHom (𝟭 C') σB W B}
  {χ : DifferentialGradedAlgebra.SemilinearHom uf σ W Z}
  {Pφ : PullbackData φ} {Eφ : Pφ.HomotopyExtension}
  {PA : PullbackData ιA} {EA : PA.HomotopyExtension}
  {PB : PullbackData ιB} {EB : PB.HomotopyExtension}
  {Pχ : PullbackData χ} {Eχ : Pχ.HomotopyExtension}

/-- The square of pullbacks of differential graded modules, descended to the homotopy categories:
`K(ιB^*) ⋙ K(φ^*) ≅ K(χ^*) ⋙ K(ιA^*)`. Descent takes a composite to the composite of the
descents, as an equality of functors, so the only step is `HomotopyCategory.descendNatIso`. -/
noncomputable def homotopyPullbackFunctorSquareIso
    (e : PB.functor ⋙ Pφ.functor ≅ Pχ.functor ⋙ PA.functor) :
    homotopyPullbackFunctor PB EB ⋙ homotopyPullbackFunctor Pφ Eφ ≅
      homotopyPullbackFunctor Pχ Eχ ⋙ homotopyPullbackFunctor PA EA :=
  eqToIso (HomotopyCategory.descend_comp PB.functor EB.preservesHomotopic Pφ.functor
      Eφ.preservesHomotopic).symm ≪≫
    HomotopyCategory.descendNatIso _ _ e ≪≫
    eqToIso (HomotopyCategory.descend_comp Pχ.functor Eχ.preservesHomotopic PA.functor
      EA.preservesHomotopic)

variable (hφ : (quasiIsomorphisms.{t, a', m} B).IsInvertedBy
    (homotopyPullbackFunctor Pφ Eφ ⋙ toDerivedCategory.{t, a, m} A))
  (hA : (quasiIsomorphisms.{t, b, m} Z).IsInvertedBy
    (homotopyPullbackFunctor PA EA ⋙ toDerivedCategory.{t, a, m} A))
  (hB : (quasiIsomorphisms.{t, b', m} W).IsInvertedBy
    (homotopyPullbackFunctor PB EB ⋙ toDerivedCategory.{t, a', m} B))
  (hχ : (quasiIsomorphisms.{t, b', m} W).IsInvertedBy
    (homotopyPullbackFunctor Pχ Eχ ⋙ toDerivedCategory.{t, b, m} Z))

/-- **The square of derived pullbacks of exact pairs**: `LιB^* ⋙ Lφ^* ≅ Lχ^* ⋙ LιA^*`. Both
composites lift `K(ιB^*) ⋙ K(φ^*)` followed by the localization — the second one through
`homotopyPullbackFunctorSquareIso` — so they agree by uniqueness of the factorisation through a
localization. This is the analogue for a square of
[Stacks, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI). -/
noncomputable def derivedPullbackOfInvertsSquareIso
    (e : PB.functor ⋙ Pφ.functor ≅ Pχ.functor ⋙ PA.functor) :
    derivedPullbackOfInverts hB ⋙ derivedPullbackOfInverts hφ ≅
      derivedPullbackOfInverts hχ ⋙ derivedPullbackOfInverts hA := by
  letI : Localization.Lifting (toDerivedCategory.{t, b', m} W) (quasiIsomorphisms.{t, b', m} W)
      ((homotopyPullbackFunctor PB EB ⋙ homotopyPullbackFunctor Pφ Eφ) ⋙
        toDerivedCategory.{t, a, m} A)
      (derivedPullbackOfInverts hB ⋙ derivedPullbackOfInverts hφ) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackComparisonIsoOfInverts hB)
        (derivedPullbackOfInverts hφ) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homotopyPullbackFunctor PB EB)
        (pullbackComparisonIsoOfInverts hφ) ≪≫
      (Functor.associator _ _ _).symm⟩
  letI : Localization.Lifting (toDerivedCategory.{t, b', m} W) (quasiIsomorphisms.{t, b', m} W)
      ((homotopyPullbackFunctor PB EB ⋙ homotopyPullbackFunctor Pφ Eφ) ⋙
        toDerivedCategory.{t, a, m} A)
      (derivedPullbackOfInverts hχ ⋙ derivedPullbackOfInverts hA) :=
    ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (pullbackComparisonIsoOfInverts hχ)
        (derivedPullbackOfInverts hA) ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (homotopyPullbackFunctor Pχ Eχ)
        (pullbackComparisonIsoOfInverts hA) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (homotopyPullbackFunctorSquareIso e).symm
        (toDerivedCategory.{t, a, m} A)⟩
  exact Localization.liftNatIso (toDerivedCategory.{t, b', m} W) (quasiIsomorphisms.{t, b', m} W)
    ((homotopyPullbackFunctor PB EB ⋙ homotopyPullbackFunctor Pφ Eφ) ⋙
      toDerivedCategory.{t, a, m} A)
    ((homotopyPullbackFunctor PB EB ⋙ homotopyPullbackFunctor Pφ Eφ) ⋙
      toDerivedCategory.{t, a, m} A)
    (derivedPullbackOfInverts hB ⋙ derivedPullbackOfInverts hφ)
    (derivedPullbackOfInverts hχ ⋙ derivedPullbackOfInverts hA) (Iso.refl _)

end Pullback

end DifferentialGradedModule

end SheafOfModules

end
