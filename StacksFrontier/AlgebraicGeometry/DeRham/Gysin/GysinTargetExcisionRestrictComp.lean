module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinTargetExcisionComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AbelianTransitionCocycle

/-!
# Transitivity of the excision for `i_*ℋ ⁿ_T` at the `restrictFunctor` spelling

`Stacks.Gysin.supportCohomologyPullbackIso_comp` is the transitivity of excision in degree `n`
along a composite of open immersions of ringed spaces.  The equation charts of
[Stacks, Tag 0G86] consume excision in the spelling
`Stacks.Gysin.supportCohomologyRestrictIso`, in which the restriction to an open subscheme is
written `AlgebraicGeometry.Scheme.Modules.restrictFunctor`.  This file carries the transitivity
across that respelling, for two nested opens `V ⊆ W ⊆ Y`.

The respelling is a conjugation: `supportCohomologyRestrictIso` *is*
`supportCohomologyPullbackIso` conjugated by `Stacks.Gysin.modulePullbackRestrictFunctorIso` at
both ends.  So the transitivity is proved once for an *arbitrary* conjugation —
`supportCohomologyConjIso_comp`, stated at a composite of open immersions of ringed spaces and
at arbitrary identifications of the two pullback functors — and the nested-opens statement is
read off it, exactly as
`Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenImmersionIso_ofRestrict_comp` is read
off `…_comp`.

## Main definitions

* `Stacks.Gysin.supportCohomologyFunctor`: `i_*ℋ ⁿ_T` as an endofunctor of the modules on a
  *ringed space*.  On a scheme it is
  `Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, by
  `supportCohomologyFunctor_eq`.
* `Stacks.Gysin.supportCohomologyConjIso`: **excision in degree `n`, conjugated by an
  identification of the pullback functor.**  For an open immersion `f` and an isomorphism
  `f^* ≅ R`, this is `Stacks.Gysin.supportCohomologyPullbackIso` read with `R` in place of `f^*`.
  `Stacks.Gysin.supportCohomologyRestrictIso` is its value at
  `Stacks.Gysin.modulePullbackRestrictFunctorIso`, by `supportCohomologyRestrictIso_eq_conj`.
* `Stacks.Gysin.modulePullbackCompConjIso`: two identifications of pullback functors and a
  factorization of the third compose to an identification of the pullback along a composite.
* `Stacks.Gysin.modulePullbackCompRestrictFunctorIso`: **pullback of modules along the nested
  ringed-space inclusion of `V ⊆ W ⊆ Y` is `restrictFunctor` along `V.ι ≫ W.ι`.**
* `Stacks.Gysin.supportCohomologyRestrictCompIso`: **the excision for the nested open `V ⊆ W`,
  at the `restrictFunctor` spelling.**

## Main results

* `Stacks.Gysin.supportCohomologyConjIso_comp`: **transitivity of the conjugated excision.**
* `Stacks.Gysin.supportCohomologyRestrictCompIso_hom`: **the nested-opens transitivity at the
  `restrictFunctor` spelling**, the statement the two-chart comparison of [Stacks, Tag 0G86]
  consumes: the excision for `V ⊆ W ⊆ Y` is the excision for `W`, restricted to `V`, followed by
  the excision for `V ⊆ W`, with the composition isomorphism
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the restriction functors mediating at
  both ends.
* `Stacks.Gysin.supportCohomologyRestrictCompIso_eq` and
  `Stacks.Gysin.supportCohomologyRestrictCompIso_inv`: the same as an equality of isomorphisms
  and read on the inverses, which is the direction `Stacks.Gysin.chartTargetHom` composes with.
* `Stacks.Gysin.isOpenImmersion_ofRestrict_comp` and
  `Stacks.Gysin.isOpenImmersion_opensRestrict_comp`: the nested inclusion of ringed spaces is an
  open immersion.

## Implementation notes

**Why the composite's instance has to be transported.**  Instance search does not find
`AlgebraicGeometry.SheafedSpace.IsOpenImmersion` of
`(W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding ≫
Y.toRingedSpace.ofRestrict W.isOpenEmbedding` for `W : Y.Opens` and `V : W.toScheme.Opens`, and
the reason is *not* that the composition instance is missing — it fires for a composite of two
variables carrying the instance, and it fires for two nested `Opens` of the underlying spaces of
a ringed space, which is `isOpenImmersion_ofRestrict_comp`.  What fails is a reducibility
mismatch in the middle: the first leg has codomain `(W.toScheme).toRingedSpace` and the second
has domain `Y.toRingedSpace.restrict W.isOpenEmbedding`, and while those are the same term —
`rfl` identifies them, which is why the composite can be written down at all — unfolding
`AlgebraicGeometry.Scheme.Opens.toScheme` is not available at the transparency instance search
runs at, so whichever of the two spellings the elaborator picks for the middle object, the other
leg's instance is then stated at a shape the `ofRestrict` instance does not match.  The fix is
`isOpenImmersion_opensRestrict_comp`: the ringed-space statement, where both legs are spelled
uniformly, transported along that `rfl`.  The same mismatch is why
`supportCohomologyRestrictCompIso_hom` supplies the two legs' instances to
`supportCohomologyConjIso_comp` by name rather than letting them be synthesized.

**The chase is isolated at an abstract category.**  `chase8` is the formal identity left over in
`supportCohomologyConjIso_comp` once the counit-free naturality squares are inserted, stated for
an arbitrary category, and `map_comp3`, `map_comp2_3` and `cancel_head` are the three pieces of
bookkeeping it needs.  This follows `GysinTargetExcisionComp.lean`: assembling the conjugation
inline does not survive the heartbeat budget of a single declaration, because `rw` and `simp`
re-typecheck their goals over derived categories of sheaves of modules.

**No declaration here carries a `@[stacks ...]` attribute**: every statement is a transport or a
coherence of one that does.

## References

* [Stacks Project, Remark 20.34.12 (Tag 0G78)](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G86](https://stacks.math.columbia.edu/tag/0G86)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedOpenImmersion
open Stacks.Cohomology.SupportedComplexes
open Stacks.Perfect.SupportedFraction
open Stacks.Perfect.SupportedQuasicoherent (derivedSupportedPushforward)

universe u

namespace Stacks.Gysin

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_modulePullback_of_isOpenImmersion

/-! ### `i_*ℋ ⁿ_T` on a ringed space -/

/-- **`i_*ℋ ⁿ_T`, as an endofunctor of the modules on a ringed space.**  The coefficient module
placed in degree `0`, its derived sections supported on `T` pushed forward to the ambient space,
and the degree-`n` cohomology sheaf of the result.  On a scheme this is
`Stacks.Perfect.SupportedFraction.supportCohomologySheafFunctor`, by
`supportCohomologyFunctor_eq`; it is introduced here only to keep the statements below
readable. -/
def supportCohomologyFunctor (X : RingedSpace.{u, u}) (T : Set X.carrier) (hT : IsClosed T)
    (n : ℤ) :
    SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X) :=
  DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing X)) 0 ⋙
    derivedSupportedPushforward X T hT ⋙
      DerivedCategory.homologyFunctor (SheafOfModules.{u} (structureSheafRing X)) n

/-- On a scheme, `supportCohomologyFunctor` is the cohomology-sheaf functor of
[Stacks, Tag 0G7Q]. -/
theorem supportCohomologyFunctor_eq {Y : Scheme.{u}} (T : Set Y) (hT : IsClosed T) (n : ℤ) :
    supportCohomologyFunctor Y.toRingedSpace T hT n = supportCohomologySheafFunctor hT n := rfl

/-! ### Excision conjugated by an identification of the pullback functor -/

section Conj

variable {X' X : RingedSpace.{u, u}} (f : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
  {R : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X')}
  (ρ : modulePullback f ≅ R) (T : Set X.carrier) (hT : IsClosed T) (n : ℤ)
  (M : SheafOfModules.{u} (structureSheafRing X))

/-- **Excision in degree `n`, conjugated by an identification of the pullback functor.**  For
`f : X' ⟶ X` an open immersion of ringed spaces, `T ⊆ X` closed and `ρ : f^* ≅ R`, this is
`Stacks.Gysin.supportCohomologyPullbackIso` read with `R` in place of `f^*` at both ends.

The spelling of excision that the equation charts of [Stacks, Tag 0G86] use,
`Stacks.Gysin.supportCohomologyRestrictIso`, is exactly this at
`ρ := Stacks.Gysin.modulePullbackRestrictFunctorIso`, by
`supportCohomologyRestrictIso_eq_conj`. -/
def supportCohomologyConjIso :
    R.obj ((supportCohomologyFunctor X T hT n).obj M) ≅
      (supportCohomologyFunctor X' (closedSubsetPreimage f T)
        (isClosed_closedSubsetPreimage f T hT) n).obj (R.obj M) :=
  (ρ.app ((supportCohomologyFunctor X T hT n).obj M)).symm ≪≫
    supportCohomologyPullbackIso f T hT n M ≪≫
      (supportCohomologyFunctor X' (closedSubsetPreimage f T)
        (isClosed_closedSubsetPreimage f T hT) n).mapIso (ρ.app M)

/-- The three factors of `supportCohomologyConjIso`, named.  True by definition. -/
theorem supportCohomologyConjIso_hom :
    (supportCohomologyConjIso f ρ T hT n M).hom =
      ρ.inv.app ((supportCohomologyFunctor X T hT n).obj M) ≫
        (supportCohomologyPullbackIso f T hT n M).hom ≫
          (supportCohomologyFunctor X' (closedSubsetPreimage f T)
            (isClosed_closedSubsetPreimage f T hT) n).map (ρ.hom.app M) := rfl

end Conj

/-- **`Stacks.Gysin.supportCohomologyRestrictIso` is the conjugated excision.**  True by
definition: both are `supportCohomologyPullbackIso` for the ringed-space inclusion of the open
subscheme, conjugated by `Stacks.Gysin.modulePullbackRestrictFunctorIso`. -/
theorem supportCohomologyRestrictIso_eq_conj {Y : Scheme.{u}} (W : Y.Opens) {T : Set Y}
    (hT : IsClosed T) (hTW : IsClosed (W.ι ⁻¹' T)) (n : ℤ) (M : Y.Modules) :
    supportCohomologyRestrictIso W hT hTW n M =
      supportCohomologyConjIso (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
        (modulePullbackRestrictFunctorIso W) T hT n M := rfl

/-! ### The identification of the pullback along a composite -/

/-- **Two identifications of pullback functors compose.**  For `f : X'' ⟶ X'` and `g : X' ⟶ X`,
isomorphisms `g^* ≅ R_g` and `f^* ≅ R_f` and a factorization `R_{fg} ≅ R_g ⋙ R_f`, the pullback
along `f ≫ g` is `R_{fg}`: the composition isomorphism
`Stacks.DerivedPullback.Composition.modulePullbackComp` of the pullbacks, the two identifications
whiskered, and the factorization. -/
def modulePullbackCompConjIso {X'' X' X : RingedSpace.{u, u}} (f : X'' ⟶ X') (g : X' ⟶ X)
    {Rg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X')}
    {Rf : SheafOfModules.{u} (structureSheafRing X') ⥤ SheafOfModules.{u} (structureSheafRing X'')}
    {Rfg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X'')}
    (ρg : modulePullback g ≅ Rg) (ρf : modulePullback f ≅ Rf) (κ : Rfg ≅ Rg ⋙ Rf) :
    modulePullback (f ≫ g) ≅ Rfg :=
  (Stacks.DerivedPullback.Composition.modulePullbackComp f g).symm ≪≫
    Functor.isoWhiskerRight ρg (modulePullback f) ≪≫
      Functor.isoWhiskerLeft Rg ρf ≪≫ κ.symm

section CompConj

variable {X'' X' X : RingedSpace.{u, u}} (f : X'' ⟶ X') (g : X' ⟶ X)
  {Rg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X')}
  {Rf : SheafOfModules.{u} (structureSheafRing X') ⥤ SheafOfModules.{u} (structureSheafRing X'')}
  {Rfg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X'')}
  (ρg : modulePullback g ≅ Rg) (ρf : modulePullback f ≅ Rf) (κ : Rfg ≅ Rg ⋙ Rf)

/-- The four factors of `modulePullbackCompConjIso`, named and right-associated. -/
theorem modulePullbackCompConjIso_hom_app
    (A : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackCompConjIso f g ρg ρf κ).hom.app A =
      (Stacks.DerivedPullback.Composition.modulePullbackComp f g).inv.app A ≫
        (modulePullback f).map (ρg.hom.app A) ≫
          ρf.hom.app (Rg.obj A) ≫ κ.inv.app A := rfl

/-- The four factors of the inverse of `modulePullbackCompConjIso`, right-associated. -/
theorem modulePullbackCompConjIso_inv_app
    (A : SheafOfModules.{u} (structureSheafRing X)) :
    (modulePullbackCompConjIso f g ρg ρf κ).inv.app A =
      κ.hom.app A ≫ ρf.inv.app (Rg.obj A) ≫
        (modulePullback f).map (ρg.inv.app A) ≫
          (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app A := by
  simp [modulePullbackCompConjIso]

end CompConj

/-! ### The formal bookkeeping, at abstract categories -/

/-- Cancelling an isomorphism against its inverse at the head of a composite.  Stated at an
arbitrary category. -/
private theorem cancel_head {D : Type*} [Category* D] {a b c : D} (m : a ⟶ b) (m' : b ⟶ a)
    (t : a ⟶ c) (h : m ≫ m' = 𝟙 a) : m ≫ m' ≫ t = t := by
  rw [← Category.assoc, h, Category.id_comp]

/-- Splitting a functor over a three-fold composite given as a hypothesis.  Stated at arbitrary
categories, for the reason given at `Stacks.Gysin.supportCohomologyConjIso_comp`.  An adapter
over `CategoryTheory.Functor.map_comp₃`: this file needs the composite supplied as a hypothesis
rather than written out, which is a different statement, but the content is the canonical one and
is not re-proved here. -/
private theorem map_comp3 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b c0 d0 : D} {m : a ⟶ d0} (x : a ⟶ b) (y : b ⟶ c0) (z : c0 ⟶ d0)
    (h : m = x ≫ y ≫ z) : F.map m = F.map x ≫ F.map y ≫ F.map z :=
  (congrArg F.map h).trans (Functor.map_comp₃ F x y z)

/-- Splitting a functor over a two-fold composite that equals a three-fold one.  Stated at
arbitrary categories. -/
private theorem map_comp2_3 {D E : Type*} [Category* D] [Category* E] (F : D ⥤ E)
    {a b c0 d0 e0 : D} {m1 : a ⟶ b} {m2 : b ⟶ e0} (x : a ⟶ c0) (y : c0 ⟶ d0) (z : d0 ⟶ e0)
    (h : m1 ≫ m2 = x ≫ y ≫ z) :
    F.map m1 ≫ F.map m2 = F.map x ≫ F.map y ≫ F.map z := by
  rw [← F.map_comp]
  exact map_comp3 F x y z h

/-- The formal identity left over in `Stacks.Gysin.supportCohomologyConjIso_comp` once the four
naturality squares, the cancellation of the composition isomorphism and the factorization of its
value at the coefficient module are inserted.  Stated at an arbitrary category, so that the
rewriting happens where no derived category appears. -/
private theorem chase8 {D : Type*} [Category* D]
    {z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 za zb zc zd ze : D}
    (k : z0 ⟶ z1) (a1 : z1 ⟶ z2) (a2 : z2 ⟶ z3) (m : z3 ⟶ z4) (m' : z4 ⟶ z3)
    (b1 : z3 ⟶ z5) (b2 : z5 ⟶ z6) (e : z6 ⟶ z7) (s : z7 ⟶ z8)
    (A1 : z1 ⟶ z9) (A2 : z9 ⟶ za) (A3 : za ⟶ zb)
    (q0 : z9 ⟶ z3) (q1 : za ⟶ z5) (q2 : zb ⟶ zc) (p1 : z5 ⟶ zc) (B2 : zc ⟶ zd)
    (E1 : z6 ⟶ zd) (E2 : zd ⟶ ze) (E3 : ze ⟶ z8)
    (hm : m ≫ m' = 𝟙 z3) (he : e ≫ s = E1 ≫ E2 ≫ E3)
    (n1 : a1 ≫ a2 = A1 ≫ q0) (n2 : q0 ≫ b1 = A2 ≫ q1)
    (n3 : A3 ≫ q2 = q1 ≫ p1) (n4 : b2 ≫ E1 = p1 ≫ B2) :
    k ≫ a1 ≫ a2 ≫ m ≫ m' ≫ b1 ≫ b2 ≫ e ≫ s =
      k ≫ A1 ≫ A2 ≫ A3 ≫ q2 ≫ B2 ≫ E2 ≫ E3 := by
  rw [reassoc_of% n1, reassoc_of% hm, reassoc_of% n2, he, reassoc_of% n4, ← reassoc_of% n3]

/-! ### Transitivity of the conjugated excision -/

/-- `supportCohomologyConjIso_hom` at a composite of open immersions, with the supporting closed
subset of the source spelled as an *iterated* preimage.  True by definition — the two spellings
are the same subset, which is `Stacks.Gysin.closedSubsetPreimage_comp` — and it is the iterated
one that `Stacks.Gysin.supportCohomologyPullbackIso_comp` and
`Stacks.Gysin.supportCohomologyPullbackIso_naturality` produce.  Keeping the two spellings apart
is not cosmetic: a goal mixing them forces the unifier to compare them at every one of the
composite's object arguments, and the heartbeat budget of
`Stacks.Gysin.supportCohomologyConjIso_comp` does not survive that. -/
private theorem supportCohomologyConjIso_hom_comp {X'' X' X : RingedSpace.{u, u}}
    (f : X'' ⟶ X') (g : X' ⟶ X) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g]
    {Rfg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X'')}
    (ρ : modulePullback (f ≫ g) ≅ Rfg) (T : Set X.carrier) (hT : IsClosed T) (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (supportCohomologyConjIso (f ≫ g) ρ T hT n M).hom =
      ρ.inv.app ((supportCohomologyFunctor X T hT n).obj M) ≫
        (supportCohomologyPullbackIso (f ≫ g) T hT n M).hom ≫
          (supportCohomologyFunctor X'' (closedSubsetPreimage f (closedSubsetPreimage g T))
            (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
              (isClosed_closedSubsetPreimage g T hT)) n).map (ρ.hom.app M) := rfl

/-- **Transitivity of the conjugated excision in degree `n`.**  For `f : X'' ⟶ X'` and
`g : X' ⟶ X` open immersions of ringed spaces, `T ⊆ X` closed, identifications `g^* ≅ R_g`,
`f^* ≅ R_f` and a factorization `κ : R_{fg} ≅ R_g ⋙ R_f`, the excision for `f ≫ g` conjugated by
`Stacks.Gysin.modulePullbackCompConjIso` is the excision for `g` conjugated by `ρg`, read inside
`R_f`, followed by the excision for `f` conjugated by `ρf` at `R_g M`, with `κ` mediating at the
source and at the target.

This is `Stacks.Gysin.supportCohomologyPullbackIso_comp` — nothing else mathematical enters.  The
two copies of the composition isomorphism of the pullbacks cancel, and what is left is the
naturality of `ρf` at the three maps the `g`-half contributes, together with **naturality of
excision in the coefficient module**, `Stacks.Gysin.supportCohomologyPullbackIso_naturality`,
which is what moves the inner factor from `g^* M` to `R_g M`. -/
theorem supportCohomologyConjIso_comp {X'' X' X : RingedSpace.{u, u}} (f : X'' ⟶ X')
    (g : X' ⟶ X) [instf : SheafedSpace.IsOpenImmersion f] [instg : SheafedSpace.IsOpenImmersion g]
    {Rg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X')}
    {Rf : SheafOfModules.{u} (structureSheafRing X') ⥤ SheafOfModules.{u} (structureSheafRing X'')}
    {Rfg : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing X'')}
    (ρg : modulePullback g ≅ Rg) (ρf : modulePullback f ≅ Rf) (κ : Rfg ≅ Rg ⋙ Rf)
    (T : Set X.carrier) (hT : IsClosed T) (n : ℤ)
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    (supportCohomologyConjIso (f ≫ g) (modulePullbackCompConjIso f g ρg ρf κ) T hT n M).hom =
      κ.hom.app ((supportCohomologyFunctor X T hT n).obj M) ≫
        Rf.map (supportCohomologyConjIso g ρg T hT n M).hom ≫
          (supportCohomologyConjIso f ρf (closedSubsetPreimage g T)
              (isClosed_closedSubsetPreimage g T hT) n (Rg.obj M)).hom ≫
            (supportCohomologyFunctor X'' (closedSubsetPreimage f (closedSubsetPreimage g T))
              (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
                (isClosed_closedSubsetPreimage g T hT)) n).map (κ.inv.app M) := by
  have hmM : (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom.app M ≫
        (modulePullbackCompConjIso f g ρg ρf κ).hom.app M =
      (modulePullback f).map (ρg.hom.app M) ≫ ρf.hom.app (Rg.obj M) ≫ κ.inv.app M := by
    rw [modulePullbackCompConjIso_hom_app]
    exact cancel_head _ _ _
      ((Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom_inv_id_app M)
  have he := map_comp2_3 (supportCohomologyFunctor X''
    (closedSubsetPreimage f (closedSubsetPreimage g T))
    (isClosed_closedSubsetPreimage f (closedSubsetPreimage g T)
      (isClosed_closedSubsetPreimage g T hT)) n) _ _ _ hmM
  have hw := map_comp3 Rf _ _ _ (supportCohomologyConjIso_hom g ρg T hT n M)
  have hm := (Stacks.DerivedPullback.Composition.modulePullbackComp f g).hom_inv_id_app
    ((supportCohomologyFunctor X T hT n).obj M)
  have n1 := (ρf.inv.naturality
    (ρg.inv.app ((supportCohomologyFunctor X T hT n).obj M))).symm
  have n2 := (ρf.inv.naturality (supportCohomologyPullbackIso g T hT n M).hom).symm
  have n3 := ρf.inv.naturality ((supportCohomologyFunctor X' (closedSubsetPreimage g T)
    (isClosed_closedSubsetPreimage g T hT) n).map (ρg.hom.app M))
  have n4 := (supportCohomologyPullbackIso_naturality f (closedSubsetPreimage g T)
    (isClosed_closedSubsetPreimage g T hT) n (ρg.hom.app M)).symm
  rw [supportCohomologyConjIso_hom_comp f g (modulePullbackCompConjIso f g ρg ρf κ) T hT n M,
    modulePullbackCompConjIso_inv_app, supportCohomologyPullbackIso_comp f g T hT n M, hw,
    supportCohomologyConjIso_hom f ρf (closedSubsetPreimage g T)
      (isClosed_closedSubsetPreimage g T hT) n (Rg.obj M)]
  dsimp only [supportCohomologyFunctor, Functor.comp_obj, Functor.comp_map] at hm he hw n1 n3 ⊢
  simp only [Category.assoc]
  exact chase8 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm he n1 n2 n3 n4

/-! ### Two nested opens of a scheme -/

section NestedOpens

/-- **The nested inclusion of ringed spaces `V' ⊆ U ⊆ X` is an open immersion.**  Stated at a
ringed space and two nested `Opens` of the underlying spaces, which is where instance search
succeeds; see the implementation notes for why the same statement at an open subscheme of an open
subscheme of a scheme has to be transported from here. -/
theorem isOpenImmersion_ofRestrict_comp (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (U' : Opens (X.restrict U.isOpenEmbedding).carrier) :
    SheafedSpace.IsOpenImmersion
      ((X.restrict U.isOpenEmbedding).ofRestrict U'.isOpenEmbedding ≫
        X.ofRestrict U.isOpenEmbedding) := inferInstance

variable {Y : Scheme.{u}} (W : Y.Opens) (V : W.toScheme.Opens)

/-- **The nested ringed-space inclusion of an open subscheme `V` of an open subscheme `W` of a
scheme `Y` is an open immersion.**  This is `isOpenImmersion_ofRestrict_comp` at
`X := Y.toRingedSpace`, transported along the identification — a `rfl` — of
`(W.toScheme).toRingedSpace` with `Y.toRingedSpace.restrict W.isOpenEmbedding`. -/
instance isOpenImmersion_opensRestrict_comp :
    SheafedSpace.IsOpenImmersion
      ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding ≫
        Y.toRingedSpace.ofRestrict W.isOpenEmbedding) :=
  isOpenImmersion_ofRestrict_comp Y.toRingedSpace W V

/-- **Pullback of modules along the nested ringed-space inclusion of `V ⊆ W ⊆ Y` is restriction
along `V.ι ≫ W.ι`.**  The two identifications
`Stacks.Gysin.modulePullbackRestrictFunctorIso` for `W` and for `V`, composed over the
composition isomorphisms of the pullbacks and of the restriction functors. -/
def modulePullbackCompRestrictFunctorIso :
    modulePullback ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding ≫
        Y.toRingedSpace.ofRestrict W.isOpenEmbedding) ≅
      Scheme.Modules.restrictFunctor (V.ι ≫ W.ι) :=
  modulePullbackCompConjIso ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding)
    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) (modulePullbackRestrictFunctorIso W)
    (modulePullbackRestrictFunctorIso V) (Scheme.Modules.restrictFunctorComp V.ι W.ι)

/-- **Excision for the nested open `V ⊆ W ⊆ Y`, at the `restrictFunctor` spelling.**  The
restriction to `V` of `i_*ℋ ⁿ_T(ℱ)` is `i''_*ℋ ⁿ_{V ∩ W ∩ T}(ℱ|_V)`, the restriction being
written along the composite `V.ι ≫ W.ι` with
`AlgebraicGeometry.Scheme.Modules.restrictFunctor`.

This is `Stacks.Gysin.supportCohomologyConjIso` for the nested ringed-space inclusion, whose
pullback is `restrictFunctor (V.ι ≫ W.ι)` by
`Stacks.Gysin.modulePullbackCompRestrictFunctorIso`; it is the composite of the excisions for `W`
and for `V ⊆ W`, by `supportCohomologyRestrictCompIso_hom`. -/
def supportCohomologyRestrictCompIso {T : Set Y} (hT : IsClosed T)
    (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (n : ℤ) (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor (V.ι ≫ W.ι)).obj
        ((supportCohomologySheafFunctor hT n).obj M) ≅
      (supportCohomologySheafFunctor hTVW n).obj
        ((Scheme.Modules.restrictFunctor (V.ι ≫ W.ι)).obj M) :=
  supportCohomologyConjIso ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding ≫
      Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
    (modulePullbackCompRestrictFunctorIso W V) T hT n M

/-- `supportCohomologyRestrictCompIso` is the conjugated excision at the composite of the two
canonical inclusions.  True by definition; it is recorded so that the transitivity can be read
off `supportCohomologyConjIso_comp` by rewriting rather than by one defeq check of the whole
statement. -/
theorem supportCohomologyRestrictCompIso_eq_conj {T : Set Y} (hT : IsClosed T)
    (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (n : ℤ) (M : Y.Modules) :
    supportCohomologyRestrictCompIso W V hT hTVW n M =
      supportCohomologyConjIso ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding ≫
          Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
        (modulePullbackCompConjIso ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding)
          (Y.toRingedSpace.ofRestrict W.isOpenEmbedding) (modulePullbackRestrictFunctorIso W)
          (modulePullbackRestrictFunctorIso V) (Scheme.Modules.restrictFunctorComp V.ι W.ι))
        T hT n M := rfl

/-- **The nested-opens transitivity of the excision for `i_*ℋ ⁿ_T`, at the `restrictFunctor`
spelling.**  For `W` an open subscheme of a scheme `Y`, `V` an open subscheme of `W`, `T ⊆ Y`
closed and `M` a module on `Y`, the excision

`(i_*ℋ ⁿ_T(M))|_V ≅ i''_*ℋ ⁿ_{V ∩ W ∩ T}(M|_V)`

of `Stacks.Gysin.supportCohomologyRestrictCompIso` is the excision for `W`, restricted to `V`,
followed by the excision for `V ⊆ W` at `M|_W`, with the composition isomorphism
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` of the restriction functors mediating at
the source and at the target.  **This is the transitivity over two nested opens that the
two-chart comparison of [Stacks, Tag 0G86] needs**, in the spelling
`Stacks.Gysin.supportCohomologyRestrictIso` that `Stacks.Gysin.chartTargetHom` uses.

It is `Stacks.Gysin.supportCohomologyConjIso_comp` at the two canonical inclusions; the two
legs' open-immersion instances are supplied by name, for the reason in the implementation
notes. -/
theorem supportCohomologyRestrictCompIso_hom {T : Set Y} (hT : IsClosed T)
    (hTW : IsClosed (W.ι ⁻¹' T)) (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (n : ℤ)
    (M : Y.Modules) :
    (supportCohomologyRestrictCompIso W V hT hTVW n M).hom =
      (Scheme.Modules.restrictFunctorComp V.ι W.ι).hom.app
          ((supportCohomologySheafFunctor hT n).obj M) ≫
        (Scheme.Modules.restrictFunctor V.ι).map
            (supportCohomologyRestrictIso W hT hTW n M).hom ≫
          (supportCohomologyRestrictIso V hTW hTVW n
              ((Scheme.Modules.restrictFunctor W.ι).obj M)).hom ≫
            (supportCohomologySheafFunctor hTVW n).map
              ((Scheme.Modules.restrictFunctorComp V.ι W.ι).inv.app M) := by
  rw [supportCohomologyRestrictCompIso_eq_conj,
    supportCohomologyRestrictIso_eq_conj W hT hTW n M,
    supportCohomologyRestrictIso_eq_conj V hTW hTVW n
      ((Scheme.Modules.restrictFunctor W.ι).obj M)]
  exact supportCohomologyConjIso_comp
    ((W.toScheme).toRingedSpace.ofRestrict V.isOpenEmbedding)
    (Y.toRingedSpace.ofRestrict W.isOpenEmbedding)
    (instf := SheafedSpace.IsOpenImmersion.ofRestrict _ V.isOpenEmbedding)
    (instg := SheafedSpace.IsOpenImmersion.ofRestrict _ W.isOpenEmbedding)
    (modulePullbackRestrictFunctorIso W) (modulePullbackRestrictFunctorIso V)
    (Scheme.Modules.restrictFunctorComp V.ι W.ι) T hT n M

/-- `supportCohomologyRestrictCompIso_hom` as an equality of **isomorphisms**, which is the form
the `.inv` direction is read off: `Stacks.Gysin.chartTargetHom` composes with the inverse of
`Stacks.Gysin.supportCohomologyRestrictIso`, not with its forward map. -/
theorem supportCohomologyRestrictCompIso_eq {T : Set Y} (hT : IsClosed T)
    (hTW : IsClosed (W.ι ⁻¹' T)) (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (n : ℤ)
    (M : Y.Modules) :
    supportCohomologyRestrictCompIso W V hT hTVW n M =
      (Scheme.Modules.restrictFunctorComp V.ι W.ι).app
          ((supportCohomologySheafFunctor hT n).obj M) ≪≫
        (Scheme.Modules.restrictFunctor V.ι).mapIso
            (supportCohomologyRestrictIso W hT hTW n M) ≪≫
          supportCohomologyRestrictIso V hTW hTVW n
              ((Scheme.Modules.restrictFunctor W.ι).obj M) ≪≫
            (supportCohomologySheafFunctor hTVW n).mapIso
              ((Scheme.Modules.restrictFunctorComp V.ι W.ι).app M).symm :=
  Iso.ext (supportCohomologyRestrictCompIso_hom W V hT hTW hTVW n M)

/-- **The nested-opens transitivity, read on the inverses.**  The inverse of the excision for
`V ⊆ W ⊆ Y` is the inverse of the excision for `V ⊆ W` at `M|_W`, then the inverse of the
excision for `W` restricted to `V`, with the composition isomorphism of the restriction functors
mediating.  This is the form `Stacks.Gysin.chartTargetHom` consumes. -/
theorem supportCohomologyRestrictCompIso_inv {T : Set Y} (hT : IsClosed T)
    (hTW : IsClosed (W.ι ⁻¹' T)) (hTVW : IsClosed (V.ι ⁻¹' (W.ι ⁻¹' T))) (n : ℤ)
    (M : Y.Modules) :
    (supportCohomologyRestrictCompIso W V hT hTVW n M).inv =
      (supportCohomologySheafFunctor hTVW n).map
          ((Scheme.Modules.restrictFunctorComp V.ι W.ι).hom.app M) ≫
        (supportCohomologyRestrictIso V hTW hTVW n
              ((Scheme.Modules.restrictFunctor W.ι).obj M)).inv ≫
          (Scheme.Modules.restrictFunctor V.ι).map
              (supportCohomologyRestrictIso W hT hTW n M).inv ≫
            (Scheme.Modules.restrictFunctorComp V.ι W.ι).inv.app
              ((supportCohomologySheafFunctor hT n).obj M) := by
  rw [supportCohomologyRestrictCompIso_eq W V hT hTW hTVW n M]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom, Iso.symm_inv,
    Category.assoc]

end NestedOpens

end Stacks.Gysin

end
