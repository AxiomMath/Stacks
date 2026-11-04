module

public import StacksFrontier.AlgebraicGeometry.Crystalline.LevelFirstOrderCrystal

/-!
# The constructed functor against the hypothesis of [Stacks, Tag 07JH]

`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFirstOrderCrystal.lean` constructs the functor of
[Stacks, Lemma 60.17.3, Tag 07JG] from the datum
`Crystalline.GlobalCrystallineSituation.SmallSite.LevelReduction07JG` and turns that datum into a
`...SmallSite.PreReduction07JG`.  This module does the two things that connect it to
[Stacks, Proposition 60.17.4, Tag 07JH]: it narrows the datum to the system of levels the tag
works over, and it factors the faithfulness half of the tag into two statements about the site.

## Main definitions

* `LevelReduction07JG.toReduction07JG` — a datum whose levels are the degree-zero member of the
  system of [Stacks, Tag 07JN] is a `...SmallSite.Reduction07JG`, which is the hypothesis bundle
  [Stacks, Tag 07JH] is stated against.

## Main results

* `LevelReduction07JG.functor07JG_toReduction07JG` — the functor of the tag at such a datum is the
  constructed functor followed by `Crystalline.firstOrderCrystalsToPairs`, so the tag is a
  statement about `...SmallSite.LevelComparison07JG.functor` and nothing else.
* `LevelComparison07JG.faithful_functor` — **the faithfulness half of [Stacks, Tag 07JH] follows
  from two statements about `Cris(X/S)`**: that a morphism of crystals is determined by its
  restrictions to the levels, and that the limit of the level sections surjects onto the sections
  over each level.
* `LevelComparison07JG.faithful_functor_of_surjective_step` — the same with the second reduced to
  surjectivity of the single steps of the tower, by
  `...SmallSite.exists_levelSectionsLimit_val_eq`.  That hypothesis is **proved** for the levels
  of [Stacks, Tag 07JN] in
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFaithfulSurjectivity.lean`, so `hdet` is the
  only stand-in the faithfulness half still carries.
* `LevelReduction07JG.faithful_functor07JG` — the same conclusion for the tag's own functor,
  through `...SmallSite.faithful_functor07JG_iff`.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no tag attribute is placed
in this module.**  Neither half
of the conclusion is discharged: `Functor.Full` and `Functor.EssSurj` of the constructed functor
are not mentioned below, and faithfulness is proved only from the two hypotheses named above.
The first of those hypotheses is a **stand-in for a result the library does not have**, so no
statement here is in the covering set of any tag:

* `hdet`, that a morphism of crystals in quasi-coherent `𝒪_{X/S}`-modules is determined by its
  restrictions to the levels, is the geometric content of the faithfulness half.  It is true in
  the source's setting because every object of `Cris(X/S)` admits a morphism to a level — `p` is
  locally nilpotent on it and the levels exhaust the `p`-adic tower.  Nothing in the tree proves
  `hdet`.  The weak finality the source's proof invokes is [Stacks, Lemma 60.5.6, Tag 07HP], which
  is `Crystalline.exists_levelEnvelope_hom` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Completed.lean`.  What stands between it
  and `hdet` is described in the module documentation of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFaithfulSurjectivity.lean`.
* `hstep`, surjectivity of each one-step restriction `Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)`, is the weaker
  of the two, and it is **no longer owed**.  The passage from it to surjectivity of the limit onto
  each level is proved here, in `...SmallSite.exists_levelSectionsLimit_val_eq`, so the hypothesis
  the factorisation carries is about one restriction map of one sheaf; and that hypothesis is
  discharged for the system of levels of [Stacks, Tag 07JN], from hypotheses (1) and (2) of that
  proposition, by `...SmallSite.surjective_levelSystem_module_map_of_eq` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/LevelFaithfulSurjectivity.lean`.  That module also
  carries the resulting form of the two statements below, with `hdet` the only stand-in left:
  `...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` and
  `...SmallSite.LevelReduction07JG.faithful_functor07JG_of_isLevel`.  It is not done in this
  module because the surjectivity lives in
  `StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelRestrictionSurjectivity.lean`, which
  is not in the import closure here.

So the value of `LevelComparison07JG.faithful_functor` is the factorisation and not the
conclusion: it says that half of [Stacks, Tag 07JH] contains exactly `hdet` on top of surjective
level restrictions, and that it contains nothing about the comparison datum, the connection, or
the four items of [Stacks, Tag 07JG].

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07KI](https://stacks.math.columbia.edu/tag/07KI)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  {L : LevelScalars07JG S D}

/-! ### Narrowing the datum to the system of levels of [Stacks, Tag 07JN] -/

section Levels

variable [IsAffine S.X] [IsAffine S.S.scheme] {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}

/-- **A datum over the system of levels of [Stacks, Tag 07JN] is a reduction datum.**  The
`...SmallSite.PreReduction07JG` of `...SmallSite.LevelReduction07JG.toPreReduction07JG` has the
datum's own system for its levels, so the field `...SmallSite.Reduction07JG.levelSystem_isLevel`
is discharged by the identity isomorphism as soon as that system is the degree-zero member of
`...SmallSite.wholeSpaceSystem`. -/
def LevelReduction07JG.toReduction07JG (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) :
    Reduction07JG S A D g Omega d p dx hp :=
  Reduction07JG.ofWholeSpaceSystem R.toPreReduction07JG hL

/-- The functor of the reduction datum `R.toReduction07JG hL` is the functor of
`R.toLevelComparison07JG`. -/
@[simp] theorem LevelReduction07JG.toReduction07JG_functor
    (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) :
    (R.toReduction07JG hL).functor = R.toLevelComparison07JG.functor :=
  rfl

/-- **The functor of [Stacks, Tag 07JG] at such a datum is the constructed one.**  So
[Stacks, Tag 07JH] at a datum built this way is a statement about
`...SmallSite.LevelComparison07JG.functor` composed with
`Crystalline.firstOrderCrystalsToPairs`, and about nothing else. -/
theorem LevelReduction07JG.functor07JG_toReduction07JG
    (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0))) :
    functor07JG (R.toReduction07JG hL) =
      R.toLevelComparison07JG.functor ⋙
        (firstOrderCrystalsToPairs A D g Omega d p dx :
          FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx ⥤
            Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d)) :=
  rfl

end Levels

/-! ### The faithfulness half, factored -/

namespace LevelComparison07JG

variable (C : LevelComparison07JG S A D g Omega d p dx L)

/-- **The faithfulness half of [Stacks, Tag 07JH] for the constructed functor, from two statements
about the site.**

`hdet` says that a morphism of crystals in quasi-coherent `𝒪_{X/S}`-modules is determined by its
restrictions to the levels, and `hsurj` that every section over a level is the component of a
compatible family.  Given both, two morphisms with the same image under the functor agree on every
section over every level, hence agree.

Neither hypothesis is about the comparison datum: the whole of this half of the tag sits in the
passage from the levels back to the site.  `hsurj` is discharged downstream — see
`faithful_functor_of_surjective_step` — and `hdet` is not discharged anywhere.  See the module
documentation for what each one amounts to. -/
theorem faithful_functor
    (hdet : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) → psi = chi)
    (hsurj : ∀ (F : QuasiCoherentCrystal S) (e : ℕ)
      (s : F.obj.val.obj (op (L.levelSystem.obj e))),
      ∃ m : L.sections F, (L.sectionsEquiv F m).val e = s) :
    Functor.Faithful C.functor where
  map_injective {F G} {psi chi} h := by
    refine hdet psi chi fun e s ↦ ?_
    obtain ⟨m, rfl⟩ := hsurj F e s
    exact congrArg (fun f : C.functor.obj F ⟶ C.functor.obj G ↦
      (L.sectionsEquiv G (f.toLinearMap m)).val e) h

/-- **The same conclusion with the second hypothesis reduced to the single steps of the tower.**
Surjectivity of each one-step restriction `Γ(T_{e + 1}, ℱ) ⟶ Γ(T_e, ℱ)` gives surjectivity of the
limit onto every level, by `...SmallSite.exists_levelSectionsLimit_val_eq`.

`hstep` is **proved** for the system of levels of [Stacks, Tag 07JN], from hypotheses (1) and (2)
of that proposition, by `...SmallSite.surjective_levelSystem_module_map_of_eq` of
`StacksFrontier/AlgebraicGeometry/Crystalline/LevelFaithfulSurjectivity.lean`, which is where the
consequence `...SmallSite.LevelComparison07JG.faithful_functor_of_isLevel` is drawn; that module
is below this one because the surjectivity lives in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelRestrictionSurjectivity.lean`, which
this module does not import.  So `hstep` is a hypothesis here only for want of an import. -/
theorem faithful_functor_of_surjective_step
    (hdet : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) → psi = chi)
    (hstep : ∀ (F : QuasiCoherentCrystal S) (e : ℕ), Function.Surjective
      (F.obj.val.map (L.levelSystem.map (homOfLE (Nat.le_succ e))).op)) :
    Functor.Faithful C.functor :=
  C.faithful_functor hdet fun F e s ↦ exists_levelSectionsLimit_val_eq (hstep F) e s

end LevelComparison07JG

/-- **The faithfulness half of [Stacks, Tag 07JH] itself, from the same two statements.**  The
passage from the constructed functor to the tag's own functor costs nothing:
`...SmallSite.faithful_functor07JG_iff` is an iff, `Crystalline.firstOrderCrystalsToPairs` being
unconditionally faithful.

This is **not** [Stacks, Tag 07JH]: the full and essentially-surjective halves are untouched
here, and `hdet` is an argument.  [Stacks, Tag 07JH] itself is
`...SmallSite.crystalPairFunctor_isEquivalence`, for the functor `...SmallSite.crystalPairFunctor`.
-/
theorem LevelReduction07JG.faithful_functor07JG [IsAffine S.X] [IsAffine S.S.scheme]
    {hp : IsNilpotent (S.p : Γ(S.X, ⊤))} (R : LevelReduction07JG S A D g Omega d p dx L)
    (hL : L.levelSystem = (wholeSpaceSystem S hp).obj (op (SimplexCategory.mk 0)))
    (hdet : ∀ {F G : QuasiCoherentCrystal S} (psi chi : F ⟶ G),
      (∀ (e : ℕ) (s : F.obj.val.obj (op (L.levelSystem.obj e))),
        (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map psi).val
            (op (L.levelSystem.obj e))).hom s =
          (PresheafOfModules.Hom.app ((quasiCoherentCrystalι S).map chi).val
            (op (L.levelSystem.obj e))).hom s) → psi = chi)
    (hstep : ∀ (F : QuasiCoherentCrystal S) (e : ℕ), Function.Surjective
      (F.obj.val.map (L.levelSystem.map (homOfLE (Nat.le_succ e))).op)) :
    Functor.Faithful (functor07JG (R.toReduction07JG hL)) :=
  (faithful_functor07JG_iff (R.toReduction07JG hL)).2
    (R.toLevelComparison07JG.faithful_functor_of_surjective_step hdet hstep)

end Crystalline.GlobalCrystallineSituation.SmallSite
