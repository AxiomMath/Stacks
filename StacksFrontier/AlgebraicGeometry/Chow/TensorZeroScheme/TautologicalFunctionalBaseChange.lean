module

public import StacksFrontier.AlgebraicGeometry.Chow.TensorZeroScheme.WholeTag
public import StacksFrontier.AlgebraicGeometry.DeRham.LineBundle.InverseSituationBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.PseudonaturalityClosure

/-!
# The tautological functional of a line bundle commutes with base change

Let `g : Y' ⟶ Y` be an arbitrary morphism of schemes, `M` an invertible `𝒪_Y`-module and
`M' = g^*M` its pullback. Write `q : L(M) ⟶ Y` and `q' : L(M') ⟶ Y'` for the two line bundles of
[Stacks, Tag 01M2] and `β : L(M') ⟶ L(M)` for the canonical morphism of
`Stacks.LineBundle.totalSpaceBaseChange`, which lies over `g`.

The fibre coordinate of `L(M)` is built from the tautological functional
`Stacks.LineBundle.Situation.tautologicalFunctional`, `q^*(M^{⊗ -1}) ⟶ 𝒪_{L(M)}`, by dualizing
twice. **This file proves the first of those four steps commutes with the base change**: the
tautological functional of `L(M')` is the tautological functional of `L(M)` pulled back along
`β`, the two sources being compared by `Stacks.Chow.TensorZeroScheme.squarePullbackMap` for the
cartesian square and by the base change of the inverse
`Stacks.LineBundle.inverseSituationPullbackIso`.

The input is `Stacks.LineBundle.totalSpaceHomEquiv_totalSpaceBaseChange`, the same statement for
the degree-one inclusion `M^{⊗ -1} ⟶ q_* 𝒪_{L(M)}` whose adjoint the tautological functional is;
what is added here is the passage across the pullback--pushforward adjunction, which is a
computation of the mate of `squarePullbackMap`.

## Main definitions

This file introduces no definitions; everything it states is about constructions already in the
library.

## Main results

* `Stacks.Mates.homEquiv_conjugateIso`: transposing a morphism precomposed with an isomorphism of
  left adjoints is transposing it and postcomposing with the conjugate isomorphism of right
  adjoints. This is `CategoryTheory.homEquiv_conjugate` read for an isomorphism rather than for a
  natural transformation, which is the form in which the three factors of
  `Stacks.Chow.TensorZeroScheme.squarePullbackMap` have known mates.
* `Stacks.LineBundle.structureComparison_eq`: the canonical map `k_* 𝒪_W ⟶ (c ≫ k)_* 𝒪_{W'}` is
  the transpose of the comparison `c^* 𝒪_W ≅ 𝒪_{W'}` of structure sheaves.
* `Stacks.LineBundle.homEquiv_squarePullbackMap`: **the transpose of a functional read through
  `squarePullbackMap`** — the mate of the comparison, factor by factor.
* `Stacks.LineBundle.homEquiv_pullback_map_unit`: the transpose of the pullback of a functional
  along the upper edge of the square.
* `Stacks.LineBundle.eq_of_homEquiv_square`: **the criterion** the two combine into: two
  functionals on the upper-left corner of a commutative square agree as soon as their transposes
  to the lower-right corner do.
* `Stacks.LineBundle.sigma_snd_eq_comp_eqToHom`: the second components of an equality of pairs in
  the functor of points, the transport along the first components written out.
* `Stacks.LineBundle.genToPushforward_totalSpaceBaseChange`:
  `Stacks.LineBundle.totalSpaceHomEquiv_totalSpaceBaseChange` read as an identity of morphisms,
  the transport along `β ≫ q = q' ≫ g` written out as an `eqToHom`.
* `Stacks.LineBundle.tautologicalFunctional_totalSpaceBaseChange`: **the tautological functional
  commutes with base change.**

## Implementation notes

The three factors of `squarePullbackMap` are `AlgebraicGeometry.Scheme.Modules.pullbackComp`
twice and `AlgebraicGeometry.Scheme.Modules.pullbackCongr` once, and the mate of each is already
known: `Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp` and
`Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackCongr`. So the transpose of a functional
precomposed with `squarePullbackMap` is computed by three applications of
`homEquiv_conjugateIso`, and what comes out is the composite of pushforward comparisons --
exactly the shape of `Stacks.LineBundle.pushforwardTransposeEquiv`.

*Why the general square lemmas are stated for arbitrary modules.* The module
`(Stacks.LineBundle.inverseSituation Y M).L` has ascribed type
`(Stacks.LineBundle.inverseSituation Y M).X.Modules`, which is `Y.Modules` by `rfl` and not
syntactically; a goal mixing the two is not type-correct at `implicit` transparency, so `rw` and
`simp` refuse it, reporting a missing pattern rather than the cause. Every rewriting step is
therefore carried out in `homEquiv_squarePullbackMap`, `homEquiv_pullback_map_unit` and
`eq_of_homEquiv_square`, where all modules are plain `Y.Modules`, and the specialization to the
line-bundle situation is a term built from `Eq.trans` and `congrArg`, whose type is checked at
default transparency. This is the device the sibling files
`StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Composite` and
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit` already use for the same
reason.

*The transport.* `Stacks.LineBundle.totalSpaceHomEquiv_totalSpaceBaseChange` is an identity of
dependent pairs whose first components are `β ≫ q` and `(𝟙 ≫ q') ≫ g`; the latter is `q' ≫ g`
definitionally, since `𝟙 ≫ k = k` holds by `rfl` for morphisms of schemes, so the only genuine
transport is the one along `β ≫ q = q' ≫ g`, and `sigma_snd_eq_comp_eqToHom` turns it into a
composition with an `eqToHom`. Any two proofs of that equality are definitionally equal, so no
compatibility between the proof `congrArg Sigma.fst` produces and
`Stacks.LineBundle.totalSpaceBaseChange_comp_lineBundleProj` has to be arranged.

*What is not here.* This is one of the four identifications the fibre coordinate
`Stacks.LineBundle.fibreCoordinate` passes through. The remaining three -- the duality
`Stacks.LineBundle.Situation.pullbackDuality` producing the tautological section from the
functional, and the two dualization isomorphisms
`Stacks.LineBundle.Situation.pullbackInverseIso` and
`Stacks.LineBundle.lineBundlePullbackIso` -- are not proved to commute with the base change. The
base-change clause of [Stacks, Tag 0F97] does **not** wait on them: it is
`Stacks.Chow.TensorZeroScheme.Decomposition.isStableUnderBaseChange`, proved by transporting an
arbitrary diagram, in which no fibre coordinate occurs. What the fibre coordinate would buy is
the finer statement that the canonically constructed diagram over `Y'` *is* the transport of the
one over `Y`. The handle on the two
dualization isomorphisms is their characterization by the duality pairings in
`StacksFrontier.AlgebraicGeometry.PullbackTensorIso.InvIsoPairing`, and what that handle lacks is
that the pullback functor is *monoidal* for `Stacks.SheafInternalHom.monoidalCategory` with
`Stacks.ProjBundleInverseBaseChange.pullbackTensorIso` as its tensorator: the pairing identity
`Stacks.TensorPowers.TensorInverse.invIso_pairing` mentions the associator and both unitors, so
transporting it along the pullback needs all three coherences.
`Stacks.PullbackSheafTensor.monoidal` is exactly that statement at the ringed-space spelling of
the monoidal structure, and the bridge between the two spellings is not built.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01M2](https://stacks.math.columbia.edu/tag/01M2)
* [Stacks Project, Tag 0F97](https://stacks.math.columbia.edu/tag/0F97)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.Chow.TensorZeroScheme (squarePullbackMap)

universe u

namespace Stacks.Mates

/-- **Transposing along an isomorphism of left adjoints.** Precomposing a morphism out of `L₁ X`
with the component at `X` of an isomorphism `L₂ ≅ L₁` and transposing along `L₂ ⊣ R₂` is
transposing along `L₁ ⊣ R₁` and postcomposing with the conjugate isomorphism `R₁ ≅ R₂`.

This is `CategoryTheory.homEquiv_conjugate` with the 2-cell presented as an isomorphism, which is
the form in which the mates of `AlgebraicGeometry.Scheme.Modules.pullbackComp` and
`AlgebraicGeometry.Scheme.Modules.pullbackCongr` are recorded. -/
theorem homEquiv_conjugateIso {C : Type*} [Category C] {D : Type*} [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : L₂ ≅ L₁) {X : C} {Z : D}
    (f : L₁.obj X ⟶ Z) :
    b.homEquiv X Z (e.hom.app X ≫ f) =
      a.homEquiv X Z f ≫ (conjugateIsoEquiv a b e).hom.app Z := by
  have h : ((conjugateEquiv a b).symm ((conjugateIsoEquiv a b e).hom)).app X = e.hom.app X :=
    congrArg (fun t => NatTrans.app t X) ((conjugateEquiv a b).symm_apply_apply e.hom)
  exact Eq.trans (congrArg (fun z => b.homEquiv X Z (z ≫ f)) h).symm
    (CategoryTheory.homEquiv_conjugate a b _ f)

end Stacks.Mates

namespace Stacks.LineBundle

open Stacks.Mates (homEquiv_conjugateIso)

/-- **The canonical map `k_* 𝒪_W ⟶ (c ≫ k)_* 𝒪_{W'}` is the transpose of the comparison of
structure sheaves.** Both are, on sections over an open `U`, the map on sections of `c`; the left
is that by definition and the right because the transpose of
`CategoryTheory.SheafOfModules.pullbackObjUnitToUnit` is
`CategoryTheory.SheafOfModules.unitToPushforwardObjUnit`, which is the comorphism on sections. -/
theorem structureComparison_eq {Z W W' : Scheme.{u}} (k : W ⟶ Z) (c : W' ⟶ W) :
    structureComparison k c =
      (Scheme.Modules.pushforward k).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv
            W.unitModule W'.unitModule (Scheme.Modules.pullbackUnitIso c).hom) ≫
        (Scheme.Modules.pushforwardComp c k).hom.app W'.unitModule := by
  have : (SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom c)).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward c).IsRightAdjoint
  have hκ : (Scheme.Modules.pullbackPushforwardAdjunction c).homEquiv
        W.unitModule W'.unitModule (Scheme.Modules.pullbackUnitIso c).hom =
      SheafOfModules.unitToPushforwardObjUnit (Scheme.Hom.toRingCatSheafHom c) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  refine Eq.trans ?_ (congrArg (fun z : W.unitModule ⟶
      (Scheme.Modules.pushforward c).obj W'.unitModule =>
    (Scheme.Modules.pushforward k).map z ≫
      (Scheme.Modules.pushforwardComp c k).hom.app W'.unitModule) hκ).symm
  exact Scheme.Modules.hom_ext _ _ fun _ => rfl

section Square

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {h : X' ⟶ X}

/-- **The transpose of the pullback of a functional along the upper edge of a square.** For a
functional `u : f^*N ⟶ 𝒪_X`, the transpose of `h^*u` followed by the comparison of structure
sheaves is the transpose of `u` followed by the canonical map `f_* 𝒪_X ⟶ (h ≫ f)_* 𝒪_{X'}`. -/
theorem homEquiv_pullback_map_unit (N : Y.Modules)
    (u : (Scheme.Modules.pullback f).obj N ⟶ X.unitModule) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).homEquiv N X'.unitModule
        ((Scheme.Modules.pullback h).map u ≫ (Scheme.Modules.pullbackUnitIso h).hom) ≫
      (Scheme.Modules.pushforwardComp h f).hom.app X'.unitModule =
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv N X.unitModule u ≫
      structureComparison f h := by
  rw [structureComparison_eq]
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Category.assoc]
  rfl

/-- **The mate of `Stacks.Chow.TensorZeroScheme.squarePullbackMap`**, read on a functional: the
transpose of a functional on the upper-left corner precomposed with the comparison is its
transpose across the right-hand and lower edges, carried to the upper and left ones by the
transport along the commutativity of the square.

Each of the three factors of the comparison contributes its own mate:
`Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp` for the two contractions of an iterated
pullback, and `Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackCongr` for the transport. -/
theorem homEquiv_squarePullbackMap (w : h ≫ f = f' ≫ g) (N : Y.Modules) (N' : Y'.Modules)
    (ι : (Scheme.Modules.pullback g).obj N ≅ N')
    (u' : (Scheme.Modules.pullback f').obj N' ⟶ X'.unitModule) :
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).homEquiv N X'.unitModule
        (squarePullbackMap w N ≫ (Scheme.Modules.pullback f').map ι.hom ≫ u') ≫
      (Scheme.Modules.pushforwardComp h f).hom.app X'.unitModule =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
        ((Scheme.Modules.pushforward f').obj X'.unitModule)
        (ι.hom ≫ (Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv N' X'.unitModule u') ≫
      (Scheme.Modules.pushforwardComp f' g).hom.app X'.unitModule) ≫
      eqToHom (congrArg (fun k : X' ⟶ Y =>
        (Scheme.Modules.pushforward k).obj X'.unitModule) w.symm) := by
  simp only [squarePullbackMap, Category.assoc]
  rw [homEquiv_conjugateIso (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)),
    Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp,
    homEquiv_conjugateIso (Scheme.Modules.pullbackPushforwardAdjunction (f' ≫ g)),
    Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackCongr,
    ← Iso.symm_hom (Scheme.Modules.pullbackComp f' g),
    homEquiv_conjugateIso ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f')),
    Stacks.Mates.conjugateIsoEquiv_iso_symm,
    Stacks.Scheme.Modules.conjugateIsoEquiv_pullbackComp, Iso.symm_symm_eq]
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_left]
  simp only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_app, Category.comp_id, eqToIso.hom,
    eqToHom_app]

/-- **Two functionals on the upper-left corner of a commutative square agree as soon as their
transposes to the lower-right corner do.** On the one side a functional `u'` on `(f')^*N'` read
back along the comparison of the square, on the other the pullback along `h` of a functional `u`
on `f^*N`; the hypothesis is the corresponding identity of transposes, between a morphism out of
`N` and the composite direct image of the structure sheaf of the upper-left corner. -/
theorem eq_of_homEquiv_square (w : h ≫ f = f' ≫ g) (N : Y.Modules) (N' : Y'.Modules)
    (ι : (Scheme.Modules.pullback g).obj N ≅ N')
    (u : (Scheme.Modules.pullback f).obj N ⟶ X.unitModule)
    (u' : (Scheme.Modules.pullback f').obj N' ⟶ X'.unitModule)
    (hyp : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv N X.unitModule u ≫
        structureComparison f h =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv N
          ((Scheme.Modules.pushforward f').obj X'.unitModule)
          (ι.hom ≫
            (Scheme.Modules.pullbackPushforwardAdjunction f').homEquiv N' X'.unitModule u') ≫
        (Scheme.Modules.pushforwardComp f' g).hom.app X'.unitModule) ≫
        eqToHom (congrArg (fun k : X' ⟶ Y =>
          (Scheme.Modules.pushforward k).obj X'.unitModule) w.symm)) :
    squarePullbackMap w N ≫ (Scheme.Modules.pullback f').map ι.hom ≫ u' =
      (Scheme.Modules.pullback h).map u ≫ (Scheme.Modules.pullbackUnitIso h).hom := by
  refine (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.pullbackPushforwardAdjunction h)).homEquiv N X'.unitModule).injective ?_
  refine (cancel_mono ((Scheme.Modules.pushforwardComp h f).hom.app X'.unitModule)).mp ?_
  rw [homEquiv_squarePullbackMap, homEquiv_pullback_map_unit, hyp]

end Square

/-- The second components of an equality of pairs in the functor of points, with the transport
along the first components written out as a composition with an `eqToHom`. -/
theorem sigma_snd_eq_comp_eqToHom {W Z : Scheme.{u}} {N : Z.Modules}
    {p p' : Σ k : W ⟶ Z, (N ⟶ (Scheme.Modules.pushforward k).obj W.unitModule)} (hp : p = p') :
    p.2 = p'.2 ≫ eqToHom (congrArg (fun j : W ⟶ Z =>
      (Scheme.Modules.pushforward j).obj W.unitModule) (congrArg Sigma.fst hp).symm) := by
  cases hp
  simp

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (M : Y.Modules)
  [hM : AlgebraicGeometry.SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property M]

include hM in
/-- **The degree-one inclusion commutes with the base change**, as an identity of morphisms
`M^{⊗ -1} ⟶ (β ≫ q)_* 𝒪_{L(M')}`. This is
`Stacks.LineBundle.totalSpaceHomEquiv_totalSpaceBaseChange`, which states it as an identity of
pairs in the functor of points, with the transport along `β ≫ q = q' ≫ g` spelled out. -/
theorem genToPushforward_totalSpaceBaseChange :
    (inverseSituation Y M).genToPushforward ≫
        structureComparison (lineBundleProj Y M) (totalSpaceBaseChange g M) =
      pushforwardTransposeEquiv g M (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))
          (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).genToPushforward ≫
        eqToHom (congrArg
          (fun k : lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M) ⟶ Y =>
            (Scheme.Modules.pushforward k).obj
              (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule)
          (totalSpaceBaseChange_comp_lineBundleProj g M).symm) :=
  sigma_snd_eq_comp_eqToHom (totalSpaceHomEquiv_totalSpaceBaseChange g M)

include hM in
/-- **The tautological functional of a line bundle commutes with arbitrary base change.** The
tautological functional `(q')^*((g^*M)^{⊗ -1}) ⟶ 𝒪_{L(g^*M)}` of the line bundle of `g^*M` is the
tautological functional `q^*(M^{⊗ -1}) ⟶ 𝒪_{L(M)}` of the line bundle of `M` pulled back along
the canonical morphism `β : L(g^*M) ⟶ L(M)`, the two sources being identified by the comparison
`Stacks.Chow.TensorZeroScheme.squarePullbackMap` of the square `β ≫ q = q' ≫ g` and the base
change of the inverse `Stacks.LineBundle.inverseSituationPullbackIso`. -/
theorem tautologicalFunctional_totalSpaceBaseChange :
    squarePullbackMap (totalSpaceBaseChange_comp_lineBundleProj g M) (inverseSituation Y M).L ≫
        (Scheme.Modules.pullback (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))).map
          (inverseSituationPullbackIso g M).hom ≫
        (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).tautologicalFunctional =
      (Scheme.Modules.pullback (totalSpaceBaseChange g M)).map
          (inverseSituation Y M).tautologicalFunctional ≫
        (Scheme.Modules.pullbackUnitIso (totalSpaceBaseChange g M)).hom := by
  refine eq_of_homEquiv_square (totalSpaceBaseChange_comp_lineBundleProj g M)
    (inverseSituation Y M).L (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L
    (inverseSituationPullbackIso g M) (inverseSituation Y M).tautologicalFunctional
    (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).tautologicalFunctional ?_
  have h1 : (Scheme.Modules.pullbackPushforwardAdjunction (lineBundleProj Y M)).homEquiv
        (inverseSituation Y M).L (lineBundleSpace Y M).unitModule
        (inverseSituation Y M).tautologicalFunctional =
      (inverseSituation Y M).genToPushforward :=
    (inverseSituation Y M).homEquiv_tautologicalFunctional
  have h2 : (Scheme.Modules.pullbackPushforwardAdjunction
          (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))).homEquiv
        (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L
        (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule
        (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).tautologicalFunctional =
      (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).genToPushforward :=
    (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).homEquiv_tautologicalFunctional
  refine Eq.trans (congrArg (fun z : (inverseSituation Y M).L ⟶
      (Scheme.Modules.pushforward (lineBundleProj Y M)).obj (lineBundleSpace Y M).unitModule =>
    z ≫ structureComparison (lineBundleProj Y M) (totalSpaceBaseChange g M)) h1) ?_
  refine Eq.trans (genToPushforward_totalSpaceBaseChange g M) ?_
  refine congrArg (fun z : (inverseSituation Y M).L ⟶
      (Scheme.Modules.pushforward
          (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M) ≫ g)).obj
        (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule =>
    z ≫ eqToHom (congrArg
      (fun k : lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M) ⟶ Y =>
        (Scheme.Modules.pushforward k).obj
          (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule)
      (totalSpaceBaseChange_comp_lineBundleProj g M).symm)) ?_
  refine Eq.trans (pushforwardTransposeEquiv_apply g M
    (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))
    (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).genToPushforward) ?_
  exact (congrArg (fun z : (inverseSituation Y' ((Scheme.Modules.pullback g).obj M)).L ⟶
      (Scheme.Modules.pushforward
          (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))).obj
        (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule =>
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv (inverseSituation Y M).L
        ((Scheme.Modules.pushforward
            (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M))).obj
          (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule)
        ((inverseSituationPullbackIso g M).hom ≫ z) ≫
      (Scheme.Modules.pushforwardComp
          (lineBundleProj Y' ((Scheme.Modules.pullback g).obj M)) g).hom.app
        (lineBundleSpace Y' ((Scheme.Modules.pullback g).obj M)).unitModule) h2).symm

end Stacks.LineBundle

end
