module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPushforwardAdjunction
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pushforward and the derived pullback of a morphism, carried as data

Let `(f, f♯) : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi, presented here as a
continuous functor `u : C' ⥤ C` in the direction opposite to `f` together with the structure map
`σ : O' ⟶ f_*O` of its sheaves of rings. Let `A` be a sheaf of differential graded `O`-algebras,
`B` one of differential graded `O'`-algebras and `φ : B ⟶ f_*A` a homomorphism. This file carries
the derived pushforward `Rf_*` and the derived pullback `Lf^*` of that situation as data, and
records the two consequences of that data which the composition statements need: the adjunction
`Lf^* ⊣ Rf_*` of [Stacks, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR), and uniqueness of
adjoints in the shape in which the source's proof of
[Stacks, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU) uses it.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.DerivedPushPullData` carries, for one morphism of
  ringed sites and one homomorphism `φ : B ⟶ f_*A`, the derived pushforward `Rf_*` and the
  derived pullback `Lf^*` together with their canonical comparison maps and the conditions
  making them the right, resp. left, derived extension of `K(f_*)`, resp. `K(f^*)` — that is,
  exactly the hypotheses of the adjunction statement
  [Stacks, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR).
* `SheafOfModules.DifferentialGradedModule.derivedPushforwardCompIsoOfAdjunctions` is
  uniqueness of adjoints in the form the source uses: from `Lf^* ⊣ Rf_*`, `Lg^* ⊣ Rg_*`,
  `L(g ∘ f)^* ⊣ R(g ∘ f)_*` and `L(g ∘ f)^* ≅ Lg^* ∘ Lf^*` it produces
  `R(g ∘ f)_* ≅ Rf_* ∘ Rg_*`.

## Main results

* `SheafOfModules.DifferentialGradedModule.DerivedPushPullData.nonempty_adjunction`: the carried
  derived pullback is left adjoint to the carried derived pushforward.

## Implementation notes

**The derived functors are parameters, as in the source and as in
`DifferentialGradedDerivedPushforwardAdjunction.lean`.** `Rf_*` and `Lf^*` are introduced by the
source as the right derived extension of `f_*` and the left derived extension of `f^*`, and
neither extension can be constructed in this development: the homotopy category of sheaves of
differential graded modules carries no triangulated structure here, so the quasi-isomorphisms are
not known to admit a calculus of fractions and the derived extensions are not known to exist.
They are therefore carried, with their comparison maps `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*` and
`α : Q' ⋙ Lf^* ⟶ K(f^*) ⋙ Q` and with the derived-value conditions of
[Stacks, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9), by `DerivedPushPullData`, whose
six fields are literally the six corresponding arguments of
`exists_adjunction_derivedPullback_derivedPushforward`. The structure is inhabited: the identity
morphism of ringed sites gives `idDerivedPushPullData`, and every pair whose direct image and
pullback invert the quasi-isomorphisms gives `derivedPushPullDataOfInverts`.

**The derived categories are the development's own.** `D(A, d)` is
`SheafOfModules.DifferentialGradedModule.derivedCategory`, the localization of the homotopy
category of right differential graded `A`-modules at the quasi-isomorphisms, so no derived
category is carried as data and the three of them do not have to be matched up across three
carried situations. The calculus-of-fractions hypotheses which the adjunction statement needs
appear as instance arguments where they are used, not as fields.

**Where Tag 0FTU is.** The source deduces `R(g ∘ f)_* = Rg_* ∘ Rf_*` from the composition of
derived pullbacks, Tag 0FTI, together with the adjunction and uniqueness of adjoints, and
`derivedPushforwardCompIsoOfAdjunctions` is that last step. The tag itself is registered in
`DifferentialGradedDerivedPushPullComposition.lean`, on
`SheafOfModules.DifferentialGradedModule.nonempty_derivedPushforward_comp_iso`, by a route that
avoids Tag 0FTI: when the two direct images of sheaves of modules are exact, all three derived
pushforwards are the factorisations of `K(f_*)`, `K(g_*)` and `K((g ∘ f)_*)` through the
localizations, and the direct image along a composition is the composite of the two direct
images already on differential graded modules.

**Continuity of a composite functor.** `Functor.isContinuous_comp` is a lemma and not an
instance — the intermediate topology cannot be inferred from the goal — so where a composite of
two continuous functors is used its continuity is an instance argument alongside continuity of
the two factors.

The universes of the sites and of their morphisms, and of the homogeneous pieces of the
algebras, are independent. The sheaves of rings share a universe because the structure maps
relate them, and the module sections share a universe because the direct image of sheaves of
modules preserves it.

## References

* [Stacks Project, Tag 0FTU](https://stacks.math.columbia.edu/tag/0FTU)
* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 0FTI](https://stacks.math.columbia.edu/tag/0FTI)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 05S9](https://stacks.math.columbia.edu/tag/05S9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a a' a'' m v u v' u' v'' u''

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### The derived pushforward and the derived pullback of one morphism, carried as data -/

section Data

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}

/-- The derived pushforward and the derived pullback of a morphism of ringed sites `f` with a
homomorphism `φ : B ⟶ f_*A` of sheaves of differential graded algebras, carried as data: the
functor `Rf_* : D(A, d) ⥤ D(B, d)` with its comparison map `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*` and the
condition that it is the right derived extension of `K(f_*)`, and the functor
`Lf^* : D(B, d) ⥤ D(A, d)` with its comparison map `α : Q' ⋙ Lf^* ⟶ K(f^*) ⋙ Q` and the
condition that it is the left derived extension of `K(f^*)`. The two conditions say that at every
object the ind-object, resp. pro-object, computing the derived value is essentially constant with
the prescribed value, and that the comparison map is its coprojection, resp. projection. -/
structure DerivedPushPullData (P : PullbackData φ) (E : P.HomotopyExtension) where
  /-- The derived pushforward `Rf_* : D(A, d) ⥤ D(B, d)`. -/
  derivedPushforward : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a', m} B
  /-- The canonical comparison map `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*`. -/
  pushforwardComparison : homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B ⟶
    toDerivedCategory.{t, a, m} A ⋙ derivedPushforward
  /-- The derived pullback `Lf^* : D(B, d) ⥤ D(A, d)`. -/
  derivedPullback : derivedCategory.{t, a', m} B ⥤ derivedCategory.{t, a, m} A
  /-- The canonical comparison map `α : Q' ⋙ Lf^* ⟶ K(f^*) ⋙ Q`. -/
  pullbackComparison : toDerivedCategory.{t, a', m} B ⋙ derivedPullback ⟶
    homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A
  /-- `Rf_*` is the right derived extension of `K(f_*)`: at every object of the homotopy category
  the ind-object computing the derived value is essentially constant with value `Rf_*` of that
  object, and `β` is its coprojection. -/
  isRightDerived (K : HomotopyCategory.{t, a, m} A) :
    ∃ (c : Cocone (MorphismProperty.Under.forget (quasiIsomorphisms.{t, a, m} A) ⊤ K ⋙
          Under.forget K ⋙ homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B))
        (_ : (homotopyPushforwardFunctor φ ⋙
          toDerivedCategory.{t, a', m} B).IsRightDerivedValueAt
            (quasiIsomorphisms.{t, a, m} A) K c)
        (ε : c.pt ≅ derivedPushforward.obj ((toDerivedCategory.{t, a, m} A).obj K)),
      ∀ s : (quasiIsomorphisms.{t, a, m} A).Under ⊤ K,
        c.ι.app s ≫ ε.hom ≫
            derivedPushforward.map ((toDerivedCategory.{t, a, m} A).map s.hom) =
          pushforwardComparison.app s.right
  /-- `Lf^*` is the left derived extension of `K(f^*)`: at every object of the homotopy category
  the pro-object computing the derived value is essentially constant with value `Lf^*` of that
  object, and `α` is its projection. -/
  isLeftDerived (M : HomotopyCategory.{t, a', m} B) :
    ∃ (d : Cone (MorphismProperty.Over.forget (quasiIsomorphisms.{t, a', m} B) ⊤ M ⋙
          Over.forget M ⋙ homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A))
        (_ : (homotopyPullbackFunctor P E ⋙
          toDerivedCategory.{t, a, m} A).IsLeftDerivedValueAt
            (quasiIsomorphisms.{t, a', m} B) M d)
        (ε : derivedPullback.obj ((toDerivedCategory.{t, a', m} B).obj M) ≅ d.pt),
      ∀ j : (quasiIsomorphisms.{t, a', m} B).Over ⊤ M,
        derivedPullback.map ((toDerivedCategory.{t, a', m} B).map j.hom) ≫ ε.hom ≫ d.π.app j =
          pullbackComparison.app j.left

/-- **The adjunction of Stacks 0FTR** read off the data: the derived pullback it carries is left
adjoint to the derived pushforward it carries. The two Ore conditions are assumptions here
because the base is an arbitrary sheaf of rings on an arbitrary site; over a ringed site they
hold by [Stacks, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4) and the tag itself is
`SheafOfModules.DifferentialGradedModule.exists_adjunction_derivedPullback_derivedPushforward`.
-/
theorem DerivedPushPullData.nonempty_adjunction
    [(quasiIsomorphisms.{t, a, m} A).HasLeftCalculusOfFractions]
    [(quasiIsomorphisms.{t, a', m} B).HasRightCalculusOfFractions]
    {P : PullbackData φ} {E : P.HomotopyExtension} (D : DerivedPushPullData P E) :
    Nonempty (D.derivedPullback ⊣ D.derivedPushforward) := by
  obtain ⟨adj, -⟩ :=
    exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions P E
    D.derivedPushforward D.pushforwardComparison D.derivedPullback D.pullbackComparison
    D.isRightDerived D.isLeftDerived
  exact ⟨adj⟩

end Data

/-! ### Derived pushforward along a composition -/

section Composition

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {C'' : Type u''} [Category.{v''} C''] {J'' : GrothendieckTopology C''}
  {R'' : Sheaf J'' RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify J'' AddCommGrpCat.{m}] [J''.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R} {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {A'' : DifferentialGradedAlgebra.{t, a''} R''}

/-- Uniqueness of adjoints, in the form in which the source uses it: if `Lf^*` is left adjoint
to `Rf_*`, if `Lg^*` is left adjoint to `Rg_*`, if `L(g ∘ f)^*` is left adjoint to `R(g ∘ f)_*`
and if `L(g ∘ f)^*` is isomorphic to `Lg^*` followed by `Lf^*`, then `R(g ∘ f)_*` is isomorphic
to `Rf_*` followed by `Rg_*`. Indeed `Lg^* ⋙ Lf^*` is left adjoint to `Rf_* ⋙ Rg_*`, so after
transporting along the given isomorphism `L(g ∘ f)^*` has both `R(g ∘ f)_*` and `Rf_* ⋙ Rg_*`
as right adjoints. -/
noncomputable def derivedPushforwardCompIsoOfAdjunctions
    {Rf : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a', m} A'}
    {Lf : derivedCategory.{t, a', m} A' ⥤ derivedCategory.{t, a, m} A}
    {Rg : derivedCategory.{t, a', m} A' ⥤ derivedCategory.{t, a'', m} A''}
    {Lg : derivedCategory.{t, a'', m} A'' ⥤ derivedCategory.{t, a', m} A'}
    {Rgf : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a'', m} A''}
    {Lgf : derivedCategory.{t, a'', m} A'' ⥤ derivedCategory.{t, a, m} A}
    (adjf : Lf ⊣ Rf) (adjg : Lg ⊣ Rg) (adjgf : Lgf ⊣ Rgf) (e : Lgf ≅ Lg ⋙ Lf) :
    Rgf ≅ Rf ⋙ Rg :=
  adjgf.rightAdjointUniq (Adjunction.ofNatIsoLeft (adjg.comp adjf) e.symm)

end Composition

end DifferentialGradedModule

end SheafOfModules

end
