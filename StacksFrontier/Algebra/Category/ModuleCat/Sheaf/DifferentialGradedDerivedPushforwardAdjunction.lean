module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoMultiplicative
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksCore.Tactic.StacksAttribute

/-!
# The derived pushforward is right adjoint to the derived pullback

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi, presented here as a
functor `u : C' ⥤ C` in the direction opposite to `f` together with the structure map
`σ : R' ⟶ f_*R` of the two sheaves of rings. Let `A` be a sheaf of differential graded
`R`-algebras on the source, let `B` be a sheaf of differential graded `R'`-algebras on the
target and let `φ : B ⟶ f_*A` be a homomorphism of sheaves of differential graded algebras.
Then the derived pushforward

`Rf_* : D(A, d) ⟶ D(B, d)`

is right adjoint to the derived pullback

`Lf^* : D(B, d) ⟶ D(A, d)`.

The source deduces this from two inputs: the adjunction `Hom(N, f_*M) = Hom(f^*N, M)` of
differential graded modules
(`SheafOfModules.DifferentialGradedModule.pullbackPushforwardAdjunction`), and the general fact
that the derived functors of an adjoint pair are adjoint
(`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`).
The step between them is that the adjunction of differential graded modules descends to the
homotopy categories, which is where the derived functors live.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.pushforwardHomotopy` is the direct image of a
  homotopy between morphisms of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.descendAdjunction` descends an
  adjunction between functors of differential graded modules, both of which preserve homotopy,
  to an adjunction between the induced functors of homotopy categories.
* `SheafOfModules.DifferentialGradedModule.homotopyPushforwardFunctor` is `K(f_*)` and
  `SheafOfModules.DifferentialGradedModule.homotopyPullbackFunctor` is `K(f^*)`.
* `SheafOfModules.DifferentialGradedModule.homotopyPullbackPushforwardAdjunction` is the
  resulting adjunction `K(f^*) ⊣ K(f_*)` of homotopy categories.

## Main results

* `SheafOfModules.DifferentialGradedModule.preservesHomotopic_pushforwardFunctor`: the direct
  image of differential graded modules carries homotopic morphisms to homotopic morphisms.
* `exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions`: the
  derived pushforward is right adjoint to the derived pullback, over an arbitrary sheaf of rings
  on an arbitrary site, with the two Ore conditions assumed.
* `SheafOfModules.DifferentialGradedModule.exists_adjunction_derivedPullback_derivedPushforward`:
  the same over a morphism of ringed sites, where the Ore conditions are automatic. This is
  [Stacks, Tag 0FTR].

## Implementation notes

**The two derived functors are parameters, as in the source.** In the source `Rf_*` and `Lf^*`
are introduced by Definitions [Stacks, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP) (2)
and [Stacks, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG) (2), as the right derived
extension of `f_*` and the left derived extension of `f^*`; the lemma formalized here is the
statement that these two functors are adjoint. Accordingly both functors are parameters,
together with their canonical comparison maps `β : K(f_*) ⋙ Q' ⟶ Q ⋙ Rf_*` and
`α : Q' ⋙ Lf^* ⟶ K(f^*) ⋙ Q`, and the hypotheses say that they *are* those derived extensions
in the sense of [Stacks, Tag 05S9]: at every object the ind-object, resp. pro-object, computing
the derived value is essentially constant with the prescribed value and the comparison maps as
its coprojections, resp. projections. This is exactly the shape of the hypotheses of
`CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt`,
which the proof then applies; no Kan extension property and no absoluteness is assumed, because
the source assumes none.

**The derived categories are the development's own.** `D(A, d)` is
`SheafOfModules.DifferentialGradedModule.derivedCategory`, the localization of the homotopy
category of right differential graded `A`-modules at the quasi-isomorphisms, and the
localization functor is `SheafOfModules.DifferentialGradedModule.toDerivedCategory`. So no
derived category is data and no model has to be matched up across the two sides of the
adjunction. The general theorem about deriving adjoints needs the quasi-isomorphisms to admit a
left, resp. right, calculus of fractions, exactly as the source's setting
[Stacks, Tag 0FNC](https://stacks.math.columbia.edu/tag/0FNC) does. Over a ringed site that is
[Stacks, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4),
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_hasLeftCalculusOfFractions` and
`...quasiIsomorphisms_hasRightCalculusOfFractions`, which rest on the triangulated structure of
[Stacks, Tag 0FS7] on `K(Mod(A, d))`; both are instances. The statement over a morphism of
ringed sites therefore assumes neither condition; the version over an arbitrary sheaf of rings on
an arbitrary site assumes them.

**The pullback is carried as data, the direct image is not.** There is no inverse image of a
sheaf of differential graded modules and no tensor product of a right differential graded module
with a differential graded bimodule here, so `f^*N = f⁻¹N ⊗_{f⁻¹B} A` cannot be written down; it
is carried as `SheafOfModules.DifferentialGradedModule.PullbackData`, as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedPullback.lean`, together with
the differential graded extension `PullbackData.HomotopyExtension` which says that it carries a
homotopy to a homotopy. The direct image, by contrast, is the *constructed* functor
`SheafOfModules.DifferentialGradedModule.pushforwardFunctor`, and that it carries a homotopy to
a homotopy is proved here rather than assumed: the direct image of a homotopy is its degreewise
direct image, because the sections of `f_*M` over `V` are the sections of `M` over `u V` on the
nose.

**Why the adjunction has to be descended by hand.** The derived functors are derived functors of
functors out of the *homotopy* category, and the quasi-isomorphisms admit a calculus of
fractions there and not in the category of differential graded modules, so the general theorem
cannot be applied to the module-level adjunction directly. Descending it is
`HomotopyCategory.descendAdjunction`: the unit and counit are the images of the module-level
unit and counit under the two quotient functors, which is well defined because every object of
the homotopy category *is* a differential graded module and every arrow is a homotopy class, and
the two triangle identities hold because they hold before passing to homotopy classes.

**A bijection on objects, not an equality of functors.** The conclusion is stated as the
existence of an adjunction `Lf^* ⊣ Rf_*` whose unit and counit are compatible with `α`, `β` and
the adjunction of homotopy categories, which is what pins it down; only existence is asserted,
as in the general theorem, since the uniqueness argument is a separate statement of the source.

The universes of the two sites and of their morphisms, of the homogeneous pieces of the two
algebras and of the objects and morphisms of the two derived categories are independent; the two
sheaves of rings share a universe because the structure map of the morphism of ringed sites
relates them, and the module sections of a sheaf and of its direct image share a universe
because the direct image of sheaves of modules preserves it.

## References

* [Stacks Project, Tag 0FTR](https://stacks.math.columbia.edu/tag/0FTR)
* [Stacks Project, Tag 0FND](https://stacks.math.columbia.edu/tag/0FND)
* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FTP](https://stacks.math.columbia.edu/tag/0FTP)
* [Stacks Project, Tag 0FTG](https://stacks.math.columbia.edu/tag/0FTG)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory

universe t t' a a' m m' v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

/-! ### The direct image of a homotopy -/

section Pushforward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}

/-- The direct image of a homotopy between morphisms of right differential graded modules: the
degreewise direct image of its components. The sections of `f_*M` over `V` are the sections of
`M` over `u V`, and a homogeneous section `b` of `B` acts through `φ b`, so each law of the
direct image homotopy is the corresponding law of the given one at `u V` and `φ b`. -/
noncomputable def pushforwardHomotopy
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A)
    {M N : DifferentialGradedModule.{t, a, m} A} {ψ χ : M ⟶ N} (h : Homotopy ψ χ) :
    Homotopy (pushforwardMap φ ψ) (pushforwardMap φ χ) where
  app n := (sitePushforward u σ).map (h.app n)
  map_mul n i V x b := h.map_mul n i (u.op.obj V) x (φ.app i V b)
  comm n := by
    change (sitePushforward u σ).map (ψ.toHomologicalComplex.f n) -
      (sitePushforward u σ).map (χ.toHomologicalComplex.f n) = _
    rw [← CategoryTheory.Functor.map_sub, h.comm n, CategoryTheory.Functor.map_add,
      CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_comp, eqToHom_map]
    rfl

/-- The direct image of right differential graded modules along a morphism of ringed sites
carries homotopic morphisms to homotopic morphisms. -/
theorem preservesHomotopic_pushforwardFunctor
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A) :
    PreservesHomotopic (pushforwardFunctor.{t, a, m} φ) :=
  fun _ _ ⟨h⟩ => ⟨pushforwardHomotopy φ h⟩

end Pushforward

/-! ### Descending an adjunction to the homotopy categories -/

section Descent

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t'}}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t', a'} R'}
  {F : DifferentialGradedModule.{t, a, m} A ⥤ DifferentialGradedModule.{t', a', m'} B}
  {G : DifferentialGradedModule.{t', a', m'} B ⥤ DifferentialGradedModule.{t, a, m} A}

namespace HomotopyCategory

/-- The unit of an adjunction of functors of differential graded modules, read on the quotient
functor out of the homotopy category: at a module it is the homotopy class of the module-level
unit. -/
def descendUnitComp (adj : G ⊣ F) (hF : PreservesHomotopic F) (hG : PreservesHomotopic G) :
    quotient B ⋙ 𝟭 (HomotopyCategory.{t', a', m'} B) ⟶
      quotient B ⋙ (descend G hG ⋙ descend F hF) where
  app M := (quotient B).map (adj.unit.app M)
  naturality M N f := by
    change (quotient B).map f ≫ (quotient B).map (adj.unit.app N) =
      (quotient B).map (adj.unit.app M) ≫ (quotient B).map (F.map (G.map f))
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (quotient B).map (adj.unit.naturality f)

/-- The counit of an adjunction of functors of differential graded modules, read on the quotient
functor out of the homotopy category: at a module it is the homotopy class of the module-level
counit. -/
def descendCounitComp (adj : G ⊣ F) (hF : PreservesHomotopic F) (hG : PreservesHomotopic G) :
    quotient A ⋙ (descend F hF ⋙ descend G hG) ⟶
      quotient A ⋙ 𝟭 (HomotopyCategory.{t, a, m} A) where
  app M := (quotient A).map (adj.counit.app M)
  naturality M N f := by
    change (quotient A).map (G.map (F.map f)) ≫ (quotient A).map (adj.counit.app N) =
      (quotient A).map (adj.counit.app M) ≫ (quotient A).map f
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact congrArg (quotient A).map (adj.counit.naturality f)

/-- An adjunction between functors of right differential graded modules which both carry
homotopic morphisms to homotopic morphisms descends to an adjunction between the induced functors
of homotopy categories. Its unit and counit are the homotopy classes of the given unit and
counit, and the triangle identities hold because they hold before passing to homotopy
classes. -/
def descendAdjunction (adj : G ⊣ F) (hF : PreservesHomotopic F) (hG : PreservesHomotopic G) :
    descend G hG ⊣ descend F hF where
  unit := CategoryTheory.Quotient.natTransLift _ (descendUnitComp adj hF hG)
  counit := CategoryTheory.Quotient.natTransLift _ (descendCounitComp adj hF hG)
  left_triangle_components X := by
    obtain ⟨M⟩ := X
    change (quotient A).map (G.map (adj.unit.app M)) ≫
      (quotient A).map (adj.counit.app (G.obj M)) = _
    rw [← CategoryTheory.Functor.map_comp]
    exact (congrArg (quotient A).map (adj.left_triangle_components M)).trans
      ((quotient A).map_id _)
  right_triangle_components Y := by
    obtain ⟨N⟩ := Y
    change (quotient B).map (adj.unit.app (F.obj N)) ≫
      (quotient B).map (F.map (adj.counit.app N)) = _
    rw [← CategoryTheory.Functor.map_comp]
    exact (congrArg (quotient B).map (adj.right_triangle_components N)).trans
      ((quotient B).map_id _)

end HomotopyCategory

end Descent

/-! ### Pull and push on the homotopy categories -/

section HomotopyPullPush

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}

/-- The functor `K(f_*) : K(Mod(A, d)) ⥤ K(Mod(B, d))` induced on the homotopy categories by the
direct image along a morphism of ringed sites. -/
noncomputable def homotopyPushforwardFunctor
    (φ : DifferentialGradedAlgebra.SemilinearHom u σ B A) :
    HomotopyCategory.{t, a, m} A ⥤ HomotopyCategory.{t, a', m} B :=
  HomotopyCategory.descend (pushforwardFunctor.{t, a, m} φ)
    (preservesHomotopic_pushforwardFunctor φ)

variable {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}

/-- The functor `K(f^*) : K(Mod(B, d)) ⥤ K(Mod(A, d))` induced on the homotopy categories by a
pullback of right differential graded modules with a differential graded extension. -/
noncomputable def homotopyPullbackFunctor (P : PullbackData φ) (E : P.HomotopyExtension) :
    HomotopyCategory.{t, a', m} B ⥤ HomotopyCategory.{t, a, m} A :=
  HomotopyCategory.descend P.functor E.preservesHomotopic

/-- The adjunction `K(f^*) ⊣ K(f_*)` of homotopy categories, descended from the adjunction
`f^* ⊣ f_*` of right differential graded modules. -/
noncomputable def homotopyPullbackPushforwardAdjunction (P : PullbackData φ)
    (E : P.HomotopyExtension) :
    homotopyPullbackFunctor P E ⊣ homotopyPushforwardFunctor φ :=
  HomotopyCategory.descendAdjunction (pullbackPushforwardAdjunction P)
    (preservesHomotopic_pushforwardFunctor φ) E.preservesHomotopic

end HomotopyPullPush

/-! ### The derived pushforward is right adjoint to the derived pullback -/

section DerivedAdjunction

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}

variable {u : C' ⥤ C} [u.IsContinuous J' J] {σ : R'.obj ⟶ u.op ⋙ R.obj}
  {A : DifferentialGradedAlgebra.{t, a} R} {B : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ B A}

/-- **The derived pushforward is right adjoint to the derived pullback**, over an arbitrary
sheaf of rings on an arbitrary site, with the two Ore conditions assumed. Let `f` be a morphism
of ringed sites, let `A` be a sheaf of differential graded algebras on its source, let `B` be
one on its target and let `φ : B ⟶ f_*A` be a homomorphism. Let `Rf_*` be the right derived
extension of the direct image and `Lf^*` the left derived extension of the pullback, each
between the derived categories `D(A, d)` and `D(B, d)`, with their canonical comparison maps
`β` and `α`. Then `Lf^*` is left adjoint to `Rf_*`, by an adjunction whose unit and counit are
compatible with `α`, `β` and the adjunction `K(f^*) ⊣ K(f_*)`.

Over a ringed site the two calculus-of-fractions assumptions are
[Stacks, Tag 0FT4](https://stacks.math.columbia.edu/tag/0FT4) and hold automatically; that is
`exists_adjunction_derivedPullback_derivedPushforward`, the form in which the tag is stated. -/
theorem exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (P : PullbackData φ) (E : P.HomotopyExtension)
    [(quasiIsomorphisms.{t, a, m} A).HasLeftCalculusOfFractions]
    [(quasiIsomorphisms.{t, a', m} B).HasRightCalculusOfFractions]
    (Rfstar : derivedCategory.{t, a, m} A ⥤ derivedCategory.{t, a', m} B)
    (β : homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{t, a', m} B ⟶
      toDerivedCategory.{t, a, m} A ⋙ Rfstar)
    (Lfstar : derivedCategory.{t, a', m} B ⥤ derivedCategory.{t, a, m} A)
    (α : toDerivedCategory.{t, a', m} B ⋙ Lfstar ⟶
      homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A)
    (hRf : ∀ K : HomotopyCategory.{t, a, m} A,
      ∃ (c : Cocone (MorphismProperty.Under.forget (quasiIsomorphisms.{t, a, m} A) ⊤ K ⋙
            Under.forget K ⋙ homotopyPushforwardFunctor φ ⋙
              toDerivedCategory.{t, a', m} B))
          (_ : (homotopyPushforwardFunctor φ ⋙
            toDerivedCategory.{t, a', m} B).IsRightDerivedValueAt
              (quasiIsomorphisms.{t, a, m} A) K c)
          (e : c.pt ≅ Rfstar.obj ((toDerivedCategory.{t, a, m} A).obj K)),
        ∀ s : (quasiIsomorphisms.{t, a, m} A).Under ⊤ K,
          c.ι.app s ≫ e.hom ≫ Rfstar.map ((toDerivedCategory.{t, a, m} A).map s.hom) =
            β.app s.right)
    (hLf : ∀ M : HomotopyCategory.{t, a', m} B,
      ∃ (d : Cone (MorphismProperty.Over.forget (quasiIsomorphisms.{t, a', m} B) ⊤ M ⋙
            Over.forget M ⋙ homotopyPullbackFunctor P E ⋙ toDerivedCategory.{t, a, m} A))
          (_ : (homotopyPullbackFunctor P E ⋙
            toDerivedCategory.{t, a, m} A).IsLeftDerivedValueAt
              (quasiIsomorphisms.{t, a', m} B) M d)
          (e : Lfstar.obj ((toDerivedCategory.{t, a', m} B).obj M) ≅ d.pt),
        ∀ j : (quasiIsomorphisms.{t, a', m} B).Over ⊤ M,
          Lfstar.map ((toDerivedCategory.{t, a', m} B).map j.hom) ≫ e.hom ≫ d.π.app j =
            α.app j.left) :
    ∃ adj : Lfstar ⊣ Rfstar,
      (∀ M : HomotopyCategory.{t, a', m} B,
          adj.unit.app ((toDerivedCategory.{t, a', m} B).obj M) ≫ Rfstar.map (α.app M) =
            (toDerivedCategory.{t, a', m} B).map
                ((homotopyPullbackPushforwardAdjunction P E).unit.app M) ≫
              β.app ((homotopyPullbackFunctor P E).obj M)) ∧
        (∀ K : HomotopyCategory.{t, a, m} A,
          Lfstar.map (β.app K) ≫ adj.counit.app ((toDerivedCategory.{t, a, m} A).obj K) =
            α.app ((homotopyPushforwardFunctor φ).obj K) ≫
              (toDerivedCategory.{t, a, m} A).map
                ((homotopyPullbackPushforwardAdjunction P E).counit.app K)) :=
  Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
    (homotopyPullbackPushforwardAdjunction P E) (quasiIsomorphisms.{t, a, m} A)
    (quasiIsomorphisms.{t, a', m} B) (toDerivedCategory.{t, a, m} A)
    (toDerivedCategory.{t, a', m} B) Rfstar β Lfstar α hRf hLf

end DerivedAdjunction

/-! ### Stacks 0FTR -/

section RingedSites

open CategoryTheory.Limits

variable {X Y : AlgebraicGeometry.RingedSite.{u, u, u}}
  {uf : Y.C ⥤ X.C} [uf.IsContinuous Y.J X.J]
  {σ : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj ⟶
    uf.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj}
  {A : DifferentialGradedAlgebra.{u, a} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : DifferentialGradedAlgebra.{u, a'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
  {φ : DifferentialGradedAlgebra.SemilinearHom uf σ B A}

/-- The derived pushforward is right adjoint to the derived pullback, for a pullback given by its
universal property. Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi,
presented by a continuous functor `uf : D ⥤ C` between two ringed sites together with the
structure map `σ` of their sheaves of rings. Let `A` be a sheaf of differential graded
`O_C`-algebras, let `B` be a sheaf of differential graded `O_D`-algebras and let `φ : B ⟶ f_*A` be
a homomorphism of sheaves of differential graded `O_D`-algebras. Let `Rf_*` be the derived
pushforward of [Stacks, Tag 0FTP] (2), the right derived extension of the direct image, and `Lf^*`
the derived pullback of [Stacks, Tag 0FTG] (2), the left derived extension of the pullback, each
between the derived categories `D(A, d)` and `D(B, d)` and each with its canonical comparison map,
`β` and `α`. Then `Lf^*` is left adjoint to `Rf_*`, by an adjunction whose unit and counit are
compatible with `α`, `β` and the adjunction `K(f^*) ⊣ K(f_*)` of homotopy categories.

The pullback `f^*M = f⁻¹M ⊗_{f⁻¹B} A` is given through the universal property that defines it,
together with its differential graded extension; the direct image is the constructed functor
`SheafOfModules.DifferentialGradedModule.pushforwardFunctor`. The proof combines the underived
adjunction `f^* ⊣ f_*` of [Stacks, Tag 0FRU], its descent to the homotopy categories, the calculus
of fractions of [Stacks, Tag 0FT4] on both sides — an instance over a ringed site, resting on the
triangulated structure of [Stacks, Tag 0FS7] — and the passage from an adjoint pair to its derived
functors, [Stacks, Tag 0FND]. -/
theorem exists_adjunction_derivedPullback_derivedPushforward
    [HasSheafify X.J AddCommGrpCat.{m}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify Y.J AddCommGrpCat.{m}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (P : PullbackData φ) (E : P.HomotopyExtension)
    (Rfstar : derivedCategory.{u, a, m} A ⥤ derivedCategory.{u, a', m} B)
    (β : homotopyPushforwardFunctor φ ⋙ toDerivedCategory.{u, a', m} B ⟶
      toDerivedCategory.{u, a, m} A ⋙ Rfstar)
    (Lfstar : derivedCategory.{u, a', m} B ⥤ derivedCategory.{u, a, m} A)
    (α : toDerivedCategory.{u, a', m} B ⋙ Lfstar ⟶
      homotopyPullbackFunctor P E ⋙ toDerivedCategory.{u, a, m} A)
    (hRf : ∀ K : HomotopyCategory.{u, a, m} A,
      ∃ (c : Cocone (MorphismProperty.Under.forget (quasiIsomorphisms.{u, a, m} A) ⊤ K ⋙
            Under.forget K ⋙ homotopyPushforwardFunctor φ ⋙
              toDerivedCategory.{u, a', m} B))
          (_ : (homotopyPushforwardFunctor φ ⋙
            toDerivedCategory.{u, a', m} B).IsRightDerivedValueAt
              (quasiIsomorphisms.{u, a, m} A) K c)
          (e : c.pt ≅ Rfstar.obj ((toDerivedCategory.{u, a, m} A).obj K)),
        ∀ s : (quasiIsomorphisms.{u, a, m} A).Under ⊤ K,
          c.ι.app s ≫ e.hom ≫ Rfstar.map ((toDerivedCategory.{u, a, m} A).map s.hom) =
            β.app s.right)
    (hLf : ∀ M : HomotopyCategory.{u, a', m} B,
      ∃ (d : Cone (MorphismProperty.Over.forget (quasiIsomorphisms.{u, a', m} B) ⊤ M ⋙
            Over.forget M ⋙ homotopyPullbackFunctor P E ⋙ toDerivedCategory.{u, a, m} A))
          (_ : (homotopyPullbackFunctor P E ⋙
            toDerivedCategory.{u, a, m} A).IsLeftDerivedValueAt
              (quasiIsomorphisms.{u, a', m} B) M d)
          (e : Lfstar.obj ((toDerivedCategory.{u, a', m} B).obj M) ≅ d.pt),
        ∀ j : (quasiIsomorphisms.{u, a', m} B).Over ⊤ M,
          Lfstar.map ((toDerivedCategory.{u, a', m} B).map j.hom) ≫ e.hom ≫ d.π.app j =
            α.app j.left) :
    ∃ adj : Lfstar ⊣ Rfstar,
      (∀ M : HomotopyCategory.{u, a', m} B,
          adj.unit.app ((toDerivedCategory.{u, a', m} B).obj M) ≫ Rfstar.map (α.app M) =
            (toDerivedCategory.{u, a', m} B).map
                ((homotopyPullbackPushforwardAdjunction P E).unit.app M) ≫
              β.app ((homotopyPullbackFunctor P E).obj M)) ∧
        (∀ K : HomotopyCategory.{u, a, m} A,
          Lfstar.map (β.app K) ≫ adj.counit.app ((toDerivedCategory.{u, a, m} A).obj K) =
            α.app ((homotopyPushforwardFunctor φ).obj K) ≫
              (toDerivedCategory.{u, a, m} A).map
                ((homotopyPullbackPushforwardAdjunction P E).counit.app K)) :=
  exists_adjunction_derivedPullback_derivedPushforward_of_hasCalculusOfFractions
    P E Rfstar β Lfstar α hRf hLf

end RingedSites

end DifferentialGradedModule

end SheafOfModules

end
