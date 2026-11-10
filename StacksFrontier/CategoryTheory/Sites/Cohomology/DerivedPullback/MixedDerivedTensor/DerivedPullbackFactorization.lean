module

public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackPreservesFlatness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackCyclesInput
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.CompositionOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.AuxiliaryRingedSite

/-!
# K-flatness and the derived pullback along the factorization of a morphism of ringed topoi

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi whose underlying continuous
functor is a morphism of sites, and let

`X --h--> X' --g--> Y`,  `X' = (C, f⁻¹O')`,

be the factorization of `StacksPullbackFactorization`.  This file records two facts about the
two halves which a derived statement about `f` needs.

First, the K-flatness assertion of Stacks 0G7E holds unconditionally: degreewise pullback along
a morphism of ringed topoi carries a K-flat complex with flat terms to a K-flat complex.  The
general statement
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` carries three hypotheses —
Stacks 05VD, Stacks 0G6R and the flatness of the cycles of an acyclic K-flat complex with flat
terms — and all three are now available, the first two for every morphism of ringed topoi and
the third for every ringed topos.  In particular `g^*` preserves K-flatness, which is the form
in which the factorization uses it: `g` is the geometric half, whose underlying continuous
functor is that of `f`, so it is a morphism of sites exactly when `f`'s is.

Second, `f` *is* the composite of the two halves, as a morphism of ringed topoi, and
consequently `Lf^* = Lg^* ∘ Lh^*`.  The underlying continuous functors compose to `f.u` on the
nose and the two structure maps compose to `f.fSharp` by
`StacksPullbackFactorization.fSharp_comp`, so the two morphisms of ringed topoi are equal;
Stacks 0D6D then gives the derived statement.  The composition formula needs both halves to be
morphisms of sites, and for `h` that costs nothing: its underlying continuous functor is the
identity of the site, whose induced functor on sheaves of sets is the identity.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.derivedPullbackFactorIso`: **`Lf^* ≅ Lg^* ⋙ Lh^*`**,
  the derived form of `StacksPullbackFactorization.pullbackFactorIso`.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.kFlat_pullbackComplex`: **the K-flatness assertion of
  Stacks 0G7E, with no hypothesis beyond the morphism-of-sites condition.**
* `Stacks.Cohomology.MixedDerivedTensor.kFlat_pullbackComplex_auxHomG`: the same for the
  geometric half `g` of the factorization, i.e. `g^*` preserves K-flatness.
* `Stacks.Cohomology.MixedDerivedTensor.isMorphismOfSites_auxHomH`: the underlying continuous
  functor of the ring-theoretic half `h` is a morphism of sites.  It is the identity functor of
  the site, and the functor it induces on sheaves of sets is the identity, which is exact.
* `Stacks.Cohomology.MixedDerivedTensor.comp_auxHom`: **`f = g ∘ h`** as morphisms of ringed
  topoi.

## Implementation notes

**Why the three hypotheses of Stacks 0G7E can be discharged here.**
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesIsFlat` is Stacks 05VD and
`AlgebraicGeometry.RingedToposSiteHom.pullbackPreservesShortExact` is Stacks 0G6R, both for an
arbitrary morphism of ringed topoi, and
`Stacks.Sheaves.DerivedPullback.KFlatPullback.cyclesIsFlat` is Stacks 0G7C for an arbitrary
ringed topos.  Nothing is reproved; the content of the first statement below is that the three
fit together.

**The equality `g ∘ h = f`.**  `AlgebraicGeometry.RingedToposSiteHom` has three fields, and two
of them cost nothing: the underlying continuous functors compose to `f.u ⋙ 𝟭 = f.u` on the nose,
and continuity is a proposition.  The structure map of the composite carries one extra factor,
the component of `CategoryTheory.Functor.sheafPushforwardContinuousComp`, which is `Iso.refl`;
removing it leaves exactly `StacksPullbackFactorization.fSharp_comp`.  The equality of the two
morphisms is then `congrArg` of the structure constructor at the structure map, which is where
the proposition-valued continuity field is absorbed.

**Universes.**  Everything is at `AlgebraicGeometry.RingedTopos.{u, u, u}`, as in
`StacksPullbackFactorization` and in the library's statements of Stacks 0G7E and 0D6D.

**No tag is placed in this file.**  Both statements are instances of results tagged where they
are proved — Stacks 0G7E in
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` and Stacks 0D6D in
`Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso` — read at the two
halves of one particular factorization.

## References

* [The Stacks Project, Tag 0G7E](https://stacks.math.columbia.edu/tag/0G7E)
* [The Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Cohomology.MixedDerivedTensor

open Stacks.Sheaves.DerivedPullback.KFlatPullback StacksPullbackFactorization

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### K-flatness of the degreewise pullback -/

/-- **The K-flatness assertion of Stacks 0G7E, with nothing left over.**  The degreewise
pullback of a K-flat complex of `O'`-modules with flat terms along a morphism of ringed topoi
whose underlying continuous functor is a morphism of sites is a K-flat complex of `O`-modules.

This is `Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` with its three
hypotheses discharged: Stacks 05VD and Stacks 0G6R hold for every morphism of ringed topoi, and
the cycles of an acyclic K-flat complex with flat terms are flat on every ringed topos. -/
theorem kFlat_pullbackComplex (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat X.O
      ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex f).obj K) :=
  Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex f hmos
    (RingedToposSiteHom.pullbackPreservesIsFlat f)
    (RingedToposSiteHom.pullbackPreservesShortExact f) (cyclesIsFlat Y) K hK hflatK

/-- **`g^*` preserves K-flatness.**  The degreewise inverse image of a K-flat complex of
`O'`-modules with flat terms, read over `f⁻¹O'` and with no change of rings, is K-flat.

The geometric half `g` of the factorization has the same underlying continuous functor as `f`,
so the morphism-of-sites hypothesis is the one already carried for `f`. -/
theorem kFlat_pullbackComplex_auxHomG (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.KFlat Y.O K)
    (hflatK : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (K.X i)) :
    Stacks.SheafOfModules.KFlat (auxTopos f).O
      ((Stacks.Sheaves.DerivedPullback.KFlatPullback.pullbackComplex (auxHomG f)).obj K) :=
  kFlat_pullbackComplex (auxHomG f) hmos K hK hflatK

/-! ### The factorization of the derived pullback -/

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- The structure map of the composite `g ∘ h` is that of `f`.  The composite's structure map
is the one of `StacksPullbackFactorization.fSharp_comp` followed by the component of
`CategoryTheory.Functor.sheafPushforwardContinuousComp`, which is `Iso.refl`. -/
lemma comp_auxHom_fSharp (f : RingedToposSiteHom X Y) :
    ((auxHomG f).comp (auxHomH f)).fSharp = f.fSharp := by
  have e : ((auxHomG f).u.sheafPushforwardContinuousComp (auxHomH f).u CommRingCat.{u}
      Y.J X.J X.J).hom.app X.O = 𝟙 _ := rfl
  dsimp only [RingedToposSiteHom.comp]
  rw [e]
  exact fSharp_comp f

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **`f = g ∘ h`.**  The two halves of the factorization compose to `f` as morphisms of ringed
topoi: their underlying continuous functors compose to `f.u` on the nose, continuity is a
proposition, and the structure maps compose to `f.fSharp` by `comp_auxHom_fSharp`. -/
theorem comp_auxHom (f : RingedToposSiteHom X Y) :
    (auxHomG f).comp (auxHomH f) = f :=
  congrArg
    (fun (t : Y.O ⟶ (f.u.sheafPushforwardContinuous CommRingCat.{u} Y.J X.J).obj X.O) ↦
      (⟨f.u, t⟩ : RingedToposSiteHom X Y)) (comp_auxHom_fSharp f)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The ring-theoretic half `h` is a morphism of sites.**  Its underlying continuous functor
is the identity of the site, and the functor the identity induces on sheaves of sets is a left
adjoint of the identity, hence the identity, which preserves finite limits. -/
theorem isMorphismOfSites_auxHomH (f : RingedToposSiteHom X Y) :
    (auxHomH f).u.IsMorphismOfSites (auxTopos f).J X.J := by
  rw [Functor.isMorphismOfSites_iff_preservesFiniteLimits]
  exact preservesFiniteLimits_of_natIso
    (Adjunction.leftAdjointUniq ((𝟭 X.C).sheafAdjunctionContinuous (Type u) X.J X.J)
      Adjunction.id).symm

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- Equal morphisms of ringed topoi have the same derived pullback.  The existence of the left
derived functor is a proposition, so the two instance arguments need no comparison. -/
lemma derivedPullback_congr {f g : RingedToposSiteHom X Y} (h : f = g)
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy g).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))] :
    derivedPullback f = derivedPullback g := by
  subst h
  rfl

/-- **`Lf^* ≅ Lg^* ⋙ Lh^*`.**  The derived pullback along `f` factors as the derived inverse
image with no change of rings, followed by the derived extension of scalars along
`f⁻¹O' ⟶ O`.

This is Stacks 0D6D at the two halves of the factorization, together with `comp_auxHom`.  It is
the derived form of `StacksPullbackFactorization.pullbackFactorIso`. -/
def derivedPullbackFactorIso (f : RingedToposSiteHom X Y)
    (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy (auxHomH f)
      (isMorphismOfSites_auxHomH f)
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy (auxHomG f) hmos
    haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
    derivedPullback (auxHomG f) ⋙ derivedPullback (auxHomH f) ≅ derivedPullback f :=
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy (auxHomH f)
    (isMorphismOfSites_auxHomH f)
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy (auxHomG f) hmos
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy f hmos
  haveI := hasLeftDerivedFunctor_pullbackOnHomotopy ((auxHomG f).comp (auxHomH f)) hmos
  Stacks.Cohomology.DerivedPullbackCompositionOnTopoi.derivedPullbackCompIso
      (auxHomH f) (auxHomG f) (isMorphismOfSites_auxHomH f) hmos ≪≫
    eqToIso (derivedPullback_congr (comp_auxHom f))

end Stacks.Cohomology.MixedDerivedTensor

end
