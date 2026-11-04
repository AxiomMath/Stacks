module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorSingleObject
public import StacksFrontier.AlgebraicGeometry.Crystalline.FiniteLevelRestrictionInjectives
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ContinuousGlobalSections

/-!
# The arrows of the tower of finite crystalline levels, and the tower

`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelTower.lean` built the terms
`RΓ(Cris(X/S_e), F_e)` of the tower of [Stacks, Tag 07MV] and
`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelRestrictionInjectives.lean` the
[Stacks, Tag 015M] comparison for the transition functors.  Both files record the same two things
as missing, and this file supplies them:

* the **underived comparison of global sections** `Γ(Cris(X/S_e), -) ⟹ ρ ⋙ Γ(Cris(X/S_m), -)`
  for `CategoryTheory.Sheaf.Γ`, which existed only for module-valued sections, as
  `...SmallSite.smallChangeBaseGlobalSectionsTrans` of `SmallSite/BaseChangeMap.lean`;
* the **composition coherence of change of divided power base**, which
  `FiniteLevelTower.lean` deliberately omitted.

With both in hand the tower is assembled, as a functor `ℕᵒᵖ ⥤ D⁺(Ab)`.

## The coherence, and why a functor `ℕᵒᵖ ⥤ D⁺(Ab)` does not need more of it

Change of divided power base does not compose on the nose: the image of an object `(U, T, δ)`
carries the structure morphism `T ⟶ S ⟶ S'`, so changing base twice gives `(T ⟶ S ⟶ S') ⟶ S''`
where changing base once along the composite gives `T ⟶ S ⟶ S''`.  These are equal only after
reassociating and using `f ≫ f' = f''`, so the two functors are isomorphic and not equal.
`smallChangeBaseCompIso` is that isomorphism; its components are the identity of the underlying
thickening, so nothing is lost.  It is proved at the generality of `smallChangeBase`, with the
two composable pairs and their composite abstract, which is also what keeps it cheap: a proof
written at the finite levels makes the kernel unfold `Crystalline.pAdicLevelSituation` and times
out.

A functor out of `ℕᵒᵖ` needs no coherence of its own beyond this.
`CategoryTheory.Functor.ofOpSequence` builds it from the successive steps `n + 1 ⟶ n` alone, so
the composite `S_k ⟶ S_m ⟶ S_e` never has to be compared with `S_k ⟶ S_e`; the one coherence
that *is* used is the one above, between the two routes from a level to `S` itself, and it is
used only to identify `ρ(F_e)` with `F_m`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.smallChangeBaseCompIso` — **change of divided power
  base composes up to canonical isomorphism**, at the generality of [Stacks, Tag 07KL].
* `Crystalline.pAdicLevelStepExtendCompIso` and
  `Crystalline.pAdicLevelStepSheafRestrictionCompIso` — that isomorphism at the finite levels,
  on the sites and then on abelian sheaves: restricting `F` to `Cris(X/S_e)` and then to
  `Cris(X/S_m)` is restricting it to `Cris(X/S_m)`.
* `Crystalline.pAdicLevelStepGlobalSectionsTrans` and `Crystalline.pAdicLevelGlobalSectionsTrans`
  — **the underived comparison on global sections** for `CategoryTheory.Sheaf.Γ`, along the
  transition `Cris(X/S_m) ⥤ Cris(X/S_e)` and along `Cris(X/S_e) ⥤ Cris(X/S)`.  They are the
  general `Stacks.Sites.globalSectionsAlongContinuous` of
  `StacksFrontier/CategoryTheory/Sites/GlobalSections/ContinuousGlobalSections.lean`, which needs
  nothing of a continuous functor of sites beyond continuity.
* `Crystalline.pAdicLevelStepDerivedGlobalSectionsMap` — **the arrow
  `RΓ(Cris(X/S_e), F_e) ⟶ RΓ(Cris(X/S_m), F_m)` of the tower**, for `m ≤ e`.
* `Crystalline.pAdicLevelDerivedGlobalSectionsTower` — **the tower
  `n ↦ RΓ(Cris(X/S_{N+n}), F_{N+n})` as a functor `ℕᵒᵖ ⥤ D⁺(Ab)`**, and
  `Crystalline.pAdicLevelDerivedGlobalSectionsTowerι` the same read in the unbounded `D(Ab)`.
* `Crystalline.pAdicLevelGlobalSectionsTower` — its underived shadow
  `n ↦ Γ(Cris(X/S_{N+n}), F_{N+n})`, a functor `ℕᵒᵖ ⥤ Ab`.

## How the derived arrow is assembled

The underived `τ : Γ(Cris(X/S_e), -) ⟹ ρ ⋙ Γ(Cris(X/S_m), -)` is derived by
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans` into
`RΓ(Cris(X/S_e), -) ⟹ R(ρ ⋙ Γ(Cris(X/S_m), -))`; the target is split by
`Crystalline.pAdicLevelStepDerivedGlobalSectionsCompIso`, which is [Stacks, Tag 015M] and is
unconditional because the restriction preserves injectives; `Rρ` is then removed from the single
complex by `CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso`, the restriction being
exact; and `ρ(F_e)` is identified with `F_m` by the coherence above.  Nothing is assumed: every
input is a hypothesis-free declaration of the library.

## Indexing: `e ≫ 0`

`Crystalline.IsPAdicLevel I γ p e` is a `Prop`, so the level situations do not depend on which
proof of it is supplied, and `Crystalline.exists_forall_isPAdicLevel` provides a threshold `N`
above which every exponent is a level.  The tower is therefore indexed by `n ↦ N + n`, taking
the family of proofs as the hypothesis `hN`.  This is the reindexing that
`FiniteLevelTower.lean` described and did not perform.

## What is and is not proved

The tower exists; **that `RΓ(Cris(X/S), F)` is its derived limit — the conclusion of
[Stacks, Tag 07MV] — is not proved and is not stated**.  What is recorded beside the tower is
only that a derived limit of it exists at all,
`Crystalline.exists_isDerivedLimit_pAdicLevelDerivedGlobalSectionsTower`, which is
`Crystalline.exists_isDerivedLimit_derivedCategory_addCommGrpCat` and says nothing about what
that limit is.  The remark's other hint, that `Γ(Cris(X/S), F) = lim_e Γ(Cris(X/S_e), F_e)`, is
likewise not proved: `pAdicLevelGlobalSectionsTrans` is the comparison map into each term of
that system, and no claim is made that the induced map to the limit is an isomorphism.

The tag attribute is placed on the two arrows and on the tower, which are what the remark
constructs, with strings saying so; the comparison maps on global sections and the coherence
isomorphism are infrastructure and carry none.  [Stacks, Tag 07MZ] is **not** tagged here and
nothing here proves any part of it: the tower below is the abelian-sheaf tower of
[Stacks, Tag 07MV], while the left tower `K` of
`...SmallSite.DerivedLimitPresentation07MZ` lives in `D(Mod_A)` and is an existentially
quantified datum there, so this is an input to that proposition and not a discharge of it.
Nothing here touches the residual recorded in `SmallSite/CompleteComparison.lean`, that
`...SmallSite.DeRhamComparison07MZ` drops the mod-`p^e` conjunct of its clause (1).

## References

* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 07MZ](https://stacks.math.columbia.edu/tag/07MZ)
* [Stacks Project, Tag 07KL](https://stacks.math.columbia.edu/tag/07KL)
* [Stacks Project, Tag 07IC](https://stacks.math.columbia.edu/tag/07IC)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w w' w'' u

namespace Crystalline

namespace GlobalCrystallineSituation

section Composition

variable (S S' S'' : GlobalCrystallineSituation.{u})
  (f : S.S ⟶ S'.S) (g : S.X ⟶ S'.X)
  (h : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f = g ≫ S'.toClosedFiber)
  (f' : S'.S ⟶ S''.S) (g' : S'.X ⟶ S''.X)
  (h' : S'.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f' = g' ≫ S''.toClosedFiber)
  {f'' : S.S ⟶ S''.S} {g'' : S.X ⟶ S''.X}
  (h'' : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap f'' = g'' ≫ S''.toClosedFiber)
  [IsOpenImmersion g] [IsOpenImmersion g'] [IsOpenImmersion g'']
  (hf : f ≫ f' = f'') (hg : g ≫ g' = g'')

/-- The comparison of the two readings of an object of `Cris(X/S)` in `Cris(X''/S'')`: changing
the divided power base twice and changing it once along the composite give the same thickening,
with the same maps to `X''` and `S''` up to the two compatibilities, so the comparison is carried
by the identity of the underlying thickening. -/
def smallChangeBaseCompHomApp (B : CrystallineThickening S) :
    (smallChangeBase S S' f g h ⋙ smallChangeBase S' S'' f' g' h').obj B ⟶
      (smallChangeBase S S'' f'' g'' h'').obj B :=
  ObjectProperty.homMk
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := by simp
      base_naturality := by
        change 𝟙 _ ≫ B.obj.toBase ≫ f'' = (B.obj.toBase ≫ f) ≫ f'
        rw [Category.id_comp, Category.assoc, hf]
      toX_naturality := by
        change 𝟙 _ ≫ B.obj.toX ≫ g'' = (B.obj.toX ≫ g) ≫ g'
        rw [Category.id_comp, Category.assoc, hg] }

/-- The comparison of `smallChangeBaseCompHomApp` in the other direction. -/
def smallChangeBaseCompInvApp (B : CrystallineThickening S) :
    (smallChangeBase S S'' f'' g'' h'').obj B ⟶
      (smallChangeBase S S' f g h ⋙ smallChangeBase S' S'' f' g' h').obj B :=
  ObjectProperty.homMk
    { sourceHom := 𝟙 _
      targetHom := 𝟙 _
      immersion_naturality := by simp
      base_naturality := by
        change 𝟙 _ ≫ (B.obj.toBase ≫ f) ≫ f' = B.obj.toBase ≫ f''
        rw [Category.id_comp, Category.assoc, hf]
      toX_naturality := by
        change 𝟙 _ ≫ (B.obj.toX ≫ g) ≫ g' = B.obj.toX ≫ g''
        rw [Category.id_comp, Category.assoc, hg] }

/-- **Change of divided power base composes, up to the canonical isomorphism carried by the
identity of the underlying thickening.**  For `(f, g) : (S, X) ⟶ (S', X')` and
`(f', g') : (S', X') ⟶ (S'', X'')` with composite `(f'', g'')`, the two functors
`Cris(X/S) ⥤ Cris(X''/S'')` agree up to a natural isomorphism whose components are the identity
on the underlying thickening.  They are *not* equal on the nose: the structure morphisms of the
image object are reassociated, `(T ⟶ S ⟶ S') ⟶ S''` against `T ⟶ S ⟶ S''`. -/
def smallChangeBaseCompIso :
    smallChangeBase S S' f g h ⋙ smallChangeBase S' S'' f' g' h' ≅
      smallChangeBase S S'' f'' g'' h'' :=
  NatIso.ofComponents
    (fun B =>
      { hom := smallChangeBaseCompHomApp S S' S'' f g h f' g' h' h'' hf hg B
        inv := smallChangeBaseCompInvApp S S' S'' f g h f' g' h' h'' hf hg B
        hom_inv_id := by
          apply ObjectProperty.hom_ext
          apply Thickening.Hom.ext <;> exact Category.comp_id _
        inv_hom_id := by
          apply ObjectProperty.hom_ext
          apply Thickening.Hom.ext <;> exact Category.comp_id _ })
    (fun k => by
      apply ObjectProperty.hom_ext
      apply Thickening.Hom.ext <;> exact (Category.comp_id _).trans (Category.id_comp _).symm)

end Composition

end GlobalCrystallineSituation

section Level

variable {A : Type u} [CommRing A] (I : Ideal A) (γ : DividedPowers I) (p : ℕ)
  [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]

open GlobalCrystallineSituation GlobalCrystallineSituation.SmallSite

/-- **The two routes from `Cris(X/S_m)` to `Cris(X/S)` agree up to canonical isomorphism**:
changing the divided power base from `S_m` to `S_e` and then to `S`, against changing it from
`S_m` to `S` directly.  This is `smallChangeBaseCompIso` at the pairs `(S_m ⟶ S_e, 𝟙 X)` and
`(S_e ⟶ S, 𝟙 X)`, whose composite is `(S_m ⟶ S, 𝟙 X)` by
`Crystalline.pAdicLevelTransitionScheme_comp_proj`. -/
def pAdicLevelStepExtendCompIso {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    pAdicLevelStepExtend I γ p hm he hme X toCF hX ⋙ pAdicLevelExtend I γ p he X toCF hX ≅
      pAdicLevelExtend I γ p hm X toCF hX :=
  smallChangeBaseCompIso (pAdicLevelSituation I γ p hm X toCF hX)
    (pAdicLevelSituation I γ p he X toCF hX) (specSituation I γ p X toCF hX)
    (pAdicLevelTransitionScheme I γ p hm he hme) (𝟙 X)
    (pAdicLevelStep_changeBase_condition I γ p hm he hme X toCF hX)
    (pAdicLevelSchemeProj I γ p he) (𝟙 X)
    (pAdicLevelSituation_changeBase_condition I γ p he X toCF hX)
    (pAdicLevelSituation_changeBase_condition I γ p hm X toCF hX)
    (pAdicLevelTransitionScheme_comp_proj I γ p hm he hme) (Category.comp_id (𝟙 X))

/-- **Restricting an abelian sheaf through an intermediate level is restricting it directly**:
`ρ(F_e) ≅ F_m` for `m ≤ e`, naturally in `F`.  Both sides are restriction along a continuous
functor, and the two functors agree by `pAdicLevelStepExtendCompIso`. -/
def pAdicLevelStepSheafRestrictionCompIso {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    pAdicLevelSheafRestriction I γ p he X toCF hX ⋙
        pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX ≅
      pAdicLevelSheafRestriction I γ p hm X toCF hX :=
  Functor.sheafPushforwardContinuousComp'
    (A := AddCommGrpCat.{u + 1}) (pAdicLevelStepExtendCompIso I γ p hm he hme X toCF hX)
    (smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
    (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
    (smallTopology (specSituation I γ p X toCF hX))

/-- **The underived comparison of global sections along the transition of the tower**, for
`CategoryTheory.Sheaf.Γ`:

`Γ(Cris(X/S_e), -) ⟹ ρ ⋙ Γ(Cris(X/S_m), -)`,

where `ρ` is `Crystalline.pAdicLevelStepSheafRestriction`.  A global section of a sheaf on
`Cris(X/S_e)` is in particular a compatible family over the objects coming from `Cris(X/S_m)`,
which is `Stacks.Sites.globalSectionsAlongContinuous` for the continuous functor of levels.  The
library had this only for module-valued sections, as
`...SmallSite.smallChangeBaseGlobalSectionsTrans`. -/
def pAdicLevelStepGlobalSectionsTrans {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    globalSections (pAdicLevelSituation I γ p he X toCF hX) ⟶
      pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX ⋙
        globalSections (pAdicLevelSituation I γ p hm X toCF hX) :=
  Stacks.Sites.globalSectionsAlongContinuous (pAdicLevelStepExtend I γ p hm he hme X toCF hX)
    (smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
    (smallTopology (pAdicLevelSituation I γ p he X toCF hX)) AddCommGrpCat.{u + 1}

/-- **The underived comparison of global sections with a finite level**,
`Γ(Cris(X/S), -) ⟹ ρ_e ⋙ Γ(Cris(X/S_e), -)`: the restriction of a global section of `F` to the
sheaf `F_e`.  These are the maps of the system whose limit the hint of [Stacks, Tag 07MV] claims
is `Γ(Cris(X/S), F)`; that it *is* the limit is not proved, here or anywhere in the library. -/
def pAdicLevelGlobalSectionsTrans {e : ℕ} (he : IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x)) :
    globalSections (specSituation I γ p X toCF hX) ⟶
      pAdicLevelSheafRestriction I γ p he X toCF hX ⋙
        globalSections (pAdicLevelSituation I γ p he X toCF hX) :=
  Stacks.Sites.globalSectionsAlongContinuous (pAdicLevelExtend I γ p he X toCF hX)
    (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
    (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}

/-! ### The derived arrows, and the tower -/

section Derived

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks Project, Tag 07MV.**  **The arrow
`RΓ(Cris(X/S_e), F_e) ⟶ RΓ(Cris(X/S_m), F_m)` of the tower of finite divided power levels**, for
`m ≤ e`.

Four inputs from the library and no hypothesis.  The underived comparison
`Crystalline.pAdicLevelStepGlobalSectionsTrans` is derived by
`Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans`; its target, the derived functor of the
composite `ρ ⋙ Γ(Cris(X/S_m), -)`, is split by
`Crystalline.pAdicLevelStepDerivedGlobalSectionsCompIso`, which is [Stacks, Tag 015M] and is
unconditional because restriction to a level preserves injectives;
`CategoryTheory.Functor.rightDerivedFunctorPlusObjSingleIso` replaces `Rρ(F_e[0])` by
`ρ(F_e)[0]`, restriction to a level being exact; and
`Crystalline.pAdicLevelStepSheafRestrictionCompIso` identifies `ρ(F_e)` with `F_m`. -/
@[stacks 07MV
  "the arrow RΓ(Cris(X/S_e), F_e) ⟶ RΓ(Cris(X/S_m), F_m) of the remark's tower, for m ≤ e"]
def pAdicLevelStepDerivedGlobalSectionsMap {m e : ℕ} (hm : IsPAdicLevel I γ p m)
    (he : IsPAdicLevel I γ p e) (hme : m ≤ e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w} (Sheaf (smallTopology (pAdicLevelSituation I γ p he X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w'} (Sheaf (smallTopology (pAdicLevelSituation I γ p hm X toCF hX))
      AddCommGrpCat.{u + 1})]
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    pAdicLevelDerivedGlobalSections I γ p he X toCF hX F ⟶
      pAdicLevelDerivedGlobalSections I γ p hm X toCF hX F :=
  (Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans
        (pAdicLevelStepGlobalSectionsTrans I γ p hm he hme X toCF hX)).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((pAdicLevelSheafRestriction I γ p he X toCF hX).obj F)) ≫
    (pAdicLevelStepDerivedGlobalSectionsCompIso I γ p hm he hme X toCF hX).hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((pAdicLevelSheafRestriction I γ p he X toCF hX).obj F)) ≫
    (derivedGlobalSectionsFunctor (pAdicLevelSituation I γ p hm X toCF hX)).map
      ((Functor.rightDerivedFunctorPlusObjSingleIso
          (pAdicLevelStepSheafRestriction I γ p hm he hme X toCF hX)
          ((pAdicLevelSheafRestriction I γ p he X toCF hX).obj F)).hom ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map
          ((pAdicLevelStepSheafRestrictionCompIso I γ p hm he hme X toCF hX).hom.app F))

/-- **Stacks Project, Tag 07MV.**  **The tower `n ↦ RΓ(Cris(X/S_{N+n}), F_{N+n})` of the remark,
as a functor `ℕᵒᵖ ⥤ D⁺(Ab)`.**

The terms are `Crystalline.pAdicLevelDerivedGlobalSections` and the arrows are
`Crystalline.pAdicLevelStepDerivedGlobalSectionsMap` at the successive pairs `N + n ≤ N + n + 1`.
`CategoryTheory.Functor.ofOpSequence` asks for no more than those successive steps, which is why
no coherence between three levels is needed.  The threshold `N` is the one of
`Crystalline.exists_forall_isPAdicLevel`: the remark's exponents are the levels, and `e ≫ 0` is
the hypothesis `hN`.

This is the tower whose derived limit the remark asserts is `RΓ(Cris(X/S), F)`.  **That
assertion is not proved**: nothing below compares the tower with `RΓ(Cris(X/S), F)`. -/
@[stacks 07MV
  "the tower e ↦ RΓ(Cris(X/S_e), F_e) of the remark, as a functor ℕᵒᵖ ⥤ D⁺(Ab); NOT the \
   remark's conclusion, that RΓ(Cris(X/S), F) is its derived limit"]
def pAdicLevelDerivedGlobalSectionsTower {N : ℕ}
    (hN : ∀ e, N ≤ e → IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    ℕᵒᵖ ⥤ DerivedCategory.Plus AddCommGrpCat.{u + 1} :=
  letI : ∀ (e : ℕ) (he : IsPAdicLevel I γ p e),
      HasDerivedCategory.{u + 2} (Sheaf (smallTopology
        (pAdicLevelSituation I γ p he X toCF hX)) AddCommGrpCat.{u + 1}) :=
    fun _ _ => hasDerivedCategorySheaf _
  Functor.ofOpSequence (X := fun n =>
      pAdicLevelDerivedGlobalSections I γ p (hN (N + n) (Nat.le_add_right N n)) X toCF hX F)
    fun n =>
      pAdicLevelStepDerivedGlobalSectionsMap I γ p (hN (N + n) (Nat.le_add_right N n))
        (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) (by omega) X toCF hX F

/-- **The tower of the remark, read in the unbounded derived category** along Mathlib's fully
faithful `CategoryTheory.DerivedCategory.Plus.ι`.  This is the shape `R lim` is taken in: the
bounded below derived category is not known to have `ℕ`-indexed products, by the module
documentation of `StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelTower.lean`. -/
def pAdicLevelDerivedGlobalSectionsTowerι {N : ℕ}
    (hN : ∀ e, N ≤ e → IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    ℕᵒᵖ ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  pAdicLevelDerivedGlobalSectionsTower I γ p hN X toCF hX F ⋙ DerivedCategory.Plus.ι

/-- **The tower of the remark has a derived limit.**  This is
`Crystalline.exists_isDerivedLimit_derivedCategory_addCommGrpCat`, which rests only on the
existence of `ℕ`-indexed products in `D(Ab)`.

It says that `R lim` of the tower exists, and **nothing about what it is**: that it is
`RΓ(Cris(X/S), F)`, which is the conclusion of [Stacks, Tag 07MV], is not proved.  The tag is
therefore not placed here. -/
theorem exists_isDerivedLimit_pAdicLevelDerivedGlobalSectionsTower {N : ℕ}
    (hN : ∀ e, N ≤ e → IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    ∃ K, CategoryTheory.Pretriangulated.IsDerivedLimit
      (pAdicLevelDerivedGlobalSectionsTowerι I γ p hN X toCF hX F) K :=
  exists_isDerivedLimit_derivedCategory_addCommGrpCat _

end Derived

/-! ### The underived shadow of the tower -/

/-- **The tower `n ↦ Γ(Cris(X/S_{N+n}), F_{N+n})` of underived global sections**, a functor
`ℕᵒᵖ ⥤ Ab`.  Its arrows are `Crystalline.pAdicLevelStepGlobalSectionsTrans` read at `F_e` and
corrected by `Crystalline.pAdicLevelStepSheafRestrictionCompIso`; it is the degree-zero shadow
of `Crystalline.pAdicLevelDerivedGlobalSectionsTower`, built from the same two inputs and
needing none of the derived machinery.

It is **not** claimed that `Γ(Cris(X/S), F)` is the limit of this tower, which is the remark's
second hint. -/
def pAdicLevelGlobalSectionsTower {N : ℕ}
    (hN : ∀ e, N ≤ e → IsPAdicLevel I γ p e) (X : Scheme.{u})
    (toCF : X ⟶ DividedPowerScheme.closedFiber (specBase I γ))
    (hX : ∀ x : X, IsNilpotent (p : X.presheaf.stalk x))
    (F : Sheaf (smallTopology (specSituation I γ p X toCF hX)) AddCommGrpCat.{u + 1}) :
    ℕᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n =>
      (globalSections (pAdicLevelSituation I γ p
          (hN (N + n) (Nat.le_add_right N n)) X toCF hX)).obj
        ((pAdicLevelSheafRestriction I γ p (hN (N + n) (Nat.le_add_right N n)) X toCF hX).obj F))
    fun n =>
      (pAdicLevelStepGlobalSectionsTrans I γ p (hN (N + n) (Nat.le_add_right N n))
            (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) (by omega) X toCF hX).app
          ((pAdicLevelSheafRestriction I γ p
            (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) X toCF hX).obj F) ≫
        (globalSections (pAdicLevelSituation I γ p
            (hN (N + n) (Nat.le_add_right N n)) X toCF hX)).map
          ((pAdicLevelStepSheafRestrictionCompIso I γ p (hN (N + n) (Nat.le_add_right N n))
            (hN (N + (n + 1)) (Nat.le_add_right N (n + 1))) (by omega) X toCF hX).hom.app F)

end Level

end Crystalline

end
