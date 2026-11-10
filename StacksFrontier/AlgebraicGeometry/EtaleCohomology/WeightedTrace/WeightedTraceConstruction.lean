module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.GroupStructure
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Weighting

/-!
# The weighted trace on geometric stalks

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `w` be an
integer-valued function on `X` and let `F` be an abelian sheaf on the small étale site of `Y`.
The stalk of `f_! f^{-1}F` at a geometric point `s` of `Y` is the direct sum over the geometric
fibre of `f` above `s` of the stalks of `f^{-1}F`, and the stalk of `f^{-1}F` at a point `x` of
that fibre is the stalk of `F` at `s`. The weighted sum `(a_x)_x ↦ ∑_x w(x) • a_x` over that
decomposition is therefore a map `(f_! f^{-1}F)_s ⟶ F_s`, and that is the behaviour on geometric
stalks which Stacks 0GKG prescribes for the trace map `Tr_{f, w}`.

This file constructs that stalk-level weighted sum and proves that a morphism of sheaves
`f_! f^{-1}F ⟶ F` realizing it is unique.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fiberPointPullbackStalkIso` — the stalk of `f^{-1}F` at a point
  of the geometric fibre above `s` is the stalk of `F` at `s`.
* `AlgebraicGeometry.SmallEtale.fiberStalkOf` — the inclusion of the summand of the stalk
  decomposition of Stacks 0F5F indexed by a point of the geometric fibre.
* `AlgebraicGeometry.SmallEtale.weightedTraceStalkMap` — the weighted sum over the geometric
  fibre, as a map out of the direct sum of stalks which the decomposition of Stacks 0F5F
  identifies with the stalk of `f_! f^{-1}F` at `s`.
* `AlgebraicGeometry.SmallEtale.HasWeightedTraceStalks` — the characterising property of the
  trace map of Stacks 0GKG: at every geometric point the map induced on stalks is that weighted
  sum.

## Main results

* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_fiberStalkOf` — the summandwise reading
  of the characterising property: on the summand indexed by a point `x` of the geometric fibre
  the trace is multiplication by the weight of `x`.
* `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_unique` — **uniqueness of the weighted
  trace.** Two morphisms `f_! f^{-1}F ⟶ F` whose effect on geometric stalks is the weighted sum
  are equal. No hypothesis on `w` is needed, in particular not that it is a weighting.
* `AlgebraicGeometry.SmallEtale.fiberPointPullbackStalkIso_natural` — the identification of the
  stalk of `f^{-1}F` above a point of the geometric fibre with the stalk of `F` below is natural
  in the abelian sheaf, which is the coherence that the functoriality of Stacks 0GKH part (1)
  asks of the trace maps, verified for the prescribed stalk data itself.
* `AlgebraicGeometry.SmallEtale.exists_hasWeightedTraceStalks_iff_presheaf` — **the existence
  half of Stacks 0GKG is equivalent to a construction on sections.** A trace map with the
  prescribed behaviour on geometric stalks exists if and only if a morphism of *presheaves*
  `f_{p!} f^{-1}F ⟶ F` with the corresponding behaviour on germs exists, where `f_{p!}` is the
  finite-support direct image presheaf of Stacks 0F6M, of which `f_!` is the sheafification;
  `AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_iff_presheaf` is the statement for a
  single morphism and its restriction along the sheafification unit.
* `AlgebraicGeometry.SmallEtale.existsUnique_hasWeightedTraceStalks_zero` — for the zero
  weighting, which is a weighting of every morphism by `AlgebraicGeometry.isWeighting_zero`, the
  trace map exists and is unique, and it is the zero morphism. This is the degenerate case of
  Stacks 0GKG, recorded because it shows the characterisation is satisfiable, so that the
  uniqueness statement above is not vacuous.

## Implementation notes

**What is here and what is not.** Stacks 0GKG asserts that for a *weighting* `w` of `f` there
*exists* a unique `Tr_{f, w} : f_! f^{-1}F ⟶ F` with the behaviour on geometric stalks above.
The uniqueness half is proved here in full generality, and the stalk-level weighted sum which
that statement refers to is constructed here. The existence half is proved, for a weighting of
an arbitrary locally quasi-finite morphism, in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceExistence`, which is
where the two halves are put together as the tag; it does not follow from anything in *this*
file: the geometric stalk functors on the small étale site of
`Y` are jointly faithful (`AlgebraicGeometry.jointlyFaithful_etaleStalkSheafFiber`, Stacks
03PU), which is what makes a morphism of sheaves determined by its stalks and hence yields
uniqueness, but they are not jointly full, so a coherent family of maps of stalks does not
assemble into a morphism of sheaves.

Existence is not a matter of a missing lemma but of a missing construction, and it is worth
recording precisely where a construction has to do work, because two routes which look similar
are not. One step of the reduction is carried out here:
`exists_hasWeightedTraceStalks_iff_presheaf` says that, `f_! f^{-1}F` being the sheafification
of the finite-support direct image presheaf `f_{p!} f^{-1}F` of Stacks 0F6M and `F` being a
sheaf, a trace map is the same thing as a morphism of presheaves `f_{p!} f^{-1}F ⟶ F` with the
same behaviour on germs. That reduction does not make the weighted sum a formula on sections:
a section of `f_{p!} G` over `V` is *not* a finite-support family of sections of `G` over the
geometric fibre. By `AlgebraicGeometry.SmallEtale.finiteSupportSections` it is a section of `G`
over a Zariski open of `X_V`, supported on a locally closed subset carrying a subscheme structure
finite over `V` (`AlgebraicGeometry.SmallEtale.IsFiniteSupport`); the description as a family
over the fibre is a statement about *stalks*, namely the germ decomposition of Stacks 0F6P
realized by `AlgebraicGeometry.SmallEtale.finiteSupportStalkIso`, and it is only available
after passing to the colimit over the étale neighbourhoods of a geometric point. The summands
`w(x) • a_x` of the weighted sum are germs of `f^{-1}F` at the points `x` of a fibre, so their
sum lies in a stalk of `F`; producing from them a *section* of `F` over `V` is exactly the
content which is missing, and it cannot be done for an arbitrary `w`: for the closed immersion
of the closed point of the spectrum of a discrete valuation ring the only weighting is the zero
function, and a trace map for the constant function `1` does not exist there, as recorded in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceLocallyQuasiFinite`.
Any correct construction must therefore use the defining property of a weighting, that the
weighted fibre sums `AlgebraicGeometry.separableDegreeWeightedFiberSum` are locally constant;
and that property delivers a *locally constant function on `V`*, which is a section of the
constant sheaf `ℤ` and not of a general `F`. This is why Stacks 0GKG builds `f_!ℤ ⟶ ℤ` first,
for the coefficient sheaf whose sections are functions, and only then passes to a general `F`
through the identification `f_! f^{-1}F ≅ f_!ℤ ⊗ F` of Stacks 0GKF.

Both of the steps that reduction needs are now carried. Stacks 0GKF is
`AlgebraicGeometry.SmallEtale.modFShriekProjectionIso` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso`, the isomorphism
`f_!F ⊗_Λ G ≅ f_!(F ⊗_Λ f^{-1}G)` for sheaves of `Λ`-modules along a locally quasi-finite `f`,
and at `Λ = ULift ℤ` the `ModuleCat`-valued and `AddCommGrpCat`-valued worlds are identified by
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleIntEquivalence`. The fibre-integral map
`f_{p!}ℤ ⟶ ℤ` is `AlgebraicGeometry.SmallEtale.integralTracePresheafMap` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTracePresheaf`, built on
`AlgebraicGeometry.fibreIntegral` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.FibreIntegral`: for a weighting `w`
of `f`, an open subscheme `U` of `X_V` and a locally constant `s : U → ℤ` supported on a closed
subscheme of `U` finite over `V`, the integral is the sum over `n` of `n` times
`∫_{U_n → V} w|_{U_n}` over the level sets of `s`, it is locally constant on `V` by
`AlgebraicGeometry.isLocallyConstant_fibreIntegral` — that is the one place the defining
property of a weighting is used — additive in `s`, independent of the part the section was taken
on, and compatible with base change of the test object by
`AlgebraicGeometry.fibreIntegral_comp_of_isPullback`. Sheafifying gives
`AlgebraicGeometry.SmallEtale.integralTrace`, whose stalk is the weighted sum by
`AlgebraicGeometry.SmallEtale.integralTrace_stalk`, and the projection formula carries it to a
general `F`.

Part (2) of Stacks 0GKH, compatibility with arbitrary base change, is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceBaseChange`, as
`AlgebraicGeometry.SmallEtale.hasWeightedTraceStalks_baseChange`. Its two inputs are the
sheaf-level base-change isomorphism `g^{-1}f_!F ≅ f'_!p^{-1}F` of Stacks 0F5J, which is
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso` and which agrees with the stalk
decompositions of Stacks 0F5F by
`AlgebraicGeometry.SmallEtale.fShriekBaseChangeNatIso_stalk`, and the comparison
`p^{-1}f^{-1}F ≅ f'^{-1}g^{-1}F` of the two iterated inverse images, which is
`AlgebraicGeometry.SmallEtale.inverseImageSquareIso`; the effect of the latter on a germ is
`AlgebraicGeometry.etaleGerm_smallEtaleSheafPullbackFactoredCompIso` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.CompGerm`, which identifies the map
it induces on a stalk with the composite of the identifications
`AlgebraicGeometry.etaleStalkSmallEtalePullObjIso`.

**The weight of a point of the geometric fibre.** A point of the geometric fibre above `s` is a
morphism from the spectrum of the algebraically closed residue field of `s` to `X` over `s`; the
weight attached to it is the value of `w` at the image of the unique point of that spectrum,
written `w (x.1 default)` as in `AlgebraicGeometry.GeometricPoint.LiesOver`.

**The transport in `fiberPointPullbackStalkIso`.** The inverse-image comparison of Stacks 03Q1
identifies the stalk of `f^{-1}F` at a geometric point `x̄` of `X` with the stalk of `F` at the
geometric point `f ∘ x̄` of `Y`. For `x̄` coming from a point of the geometric fibre above `s`
the geometric point `f ∘ x̄` *is* `s`, but only propositionally, by the defining property of a
point of the fibre; `toGeometricPoint_map` records that equality of geometric points and the
comparison is composed with the identification of stalks it induces.
`AlgebraicGeometry.etaleStalk_eqToHom_naturality` is the one lemma needed to move a morphism of
presheaves across such an identification, and it is proved by cases on the equality of points,
so no reasoning about `eqToHom` is left in the proofs below.

**Decidability of the index.** The geometric fibre carries no decidable equality, so the
inclusion of a summand of the direct sum of stalks and the map out of it given by a family are
available only after choosing one. The choice is made once and for all, inside `fiberStalkOf`
and `weightedTraceStalkMap`, so that it never appears in a statement.

## References

* [Stacks Project, Tag 0GKG](https://stacks.math.columbia.edu/tag/0GKG)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 03PU](https://stacks.math.columbia.edu/tag/03PU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace AlgebraicGeometry

section Transport

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Moving a morphism of presheaves across the identification of the stalks at two equal
geometric points. -/
public theorem etaleStalk_eqToHom_naturality {t t' : GeometricPoint S} (h : t = t')
    {P Q : (SmallEtale B S hS)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v}} (φ : P ⟶ Q) :
    eqToHom (congrArg (fun r => etaleStalk B S hS r P) h) ≫
        colim.map (Functor.whiskerLeft (Functor.Elements.π
          (geometricPointFiber B S hS t')).op φ) =
      colim.map (Functor.whiskerLeft (Functor.Elements.π
          (geometricPointFiber B S hS t)).op φ) ≫
        eqToHom (congrArg (fun r => etaleStalk B S hS r Q) h) := by
  cases h
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end Transport

namespace SmallEtale

section FiberPoint

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)

/-- A point of the geometric fibre of `f` above a geometric point `s` of `Y` composes with `f`
to `s` itself. -/
public theorem toGeometricPoint_map (s : GeometricPoint Y.obj)
    (x : GeometricFiberPoint B f s) :
    (x.toGeometricPoint B f s).map (B.inclusion.map f) = s := by
  obtain ⟨p, hp⟩ := x
  exact congrArg
    (fun m => ({ residueField := s.residueField, hom := m } : GeometricPoint Y.obj)) hp

/-- **Stacks 03Q1 above a point of the geometric fibre.** The stalk of the inverse image
`f^{-1}F` at a point `x` of the geometric fibre of `f` above a geometric point `s` of `Y` is the
stalk of `F` at `s`. -/
public def fiberPointPullbackStalkIso (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B f s) :
    etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
        ((abPullback.{u, v} B f).obj F).obj ≅
      etaleStalk B Y.obj Y.property s F.obj :=
  etaleStalkSmallEtalePullObjIso B f (x.toGeometricPoint B f s)
      AddCommGrpCat.{max (u + 1) v} F ≪≫
    eqToIso (congrArg (fun r => etaleStalk B Y.obj Y.property r F.obj)
      (toGeometricPoint_map B f s x))

/-- The identification of the stalk of `f^{-1}F` at a point of the geometric fibre with the
stalk of `F` at the geometric point below it is natural in the abelian sheaf. -/
public theorem fiberPointPullbackStalkIso_natural (s : GeometricPoint Y.obj)
    {F G : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}}
    (φ : F ⟶ G) (x : GeometricFiberPoint B f s) :
    colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B X.obj X.property
            (x.toGeometricPoint B f s))).op ((abPullback.{u, v} B f).map φ).1) ≫
        (fiberPointPullbackStalkIso.{u, v} B f s G x).hom =
      (fiberPointPullbackStalkIso.{u, v} B f s F x).hom ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op φ.1) := by
  have hnat := (smallEtalePullbackSheafFiberIso B f (x.toGeometricPoint B f s)
    AddCommGrpCat.{max (u + 1) v}).hom.naturality φ
  have htr := etaleStalk_eqToHom_naturality.{u, v} B Y.obj Y.property
    (toGeometricPoint_map B f s x) φ.1
  exact ((Category.assoc _ _ _).trans
    ((congrArg (fun m => (etaleStalkSmallEtalePullObjIso B f (x.toGeometricPoint B f s)
          AddCommGrpCat.{max (u + 1) v} F).hom ≫ m) htr).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun m => m ≫ eqToHom
              (congrArg (fun r => etaleStalk B Y.obj Y.property r G.obj)
                (toGeometricPoint_map B f s x))) hnat.symm).trans
          (Category.assoc _ _ _))))).symm

/-- The inclusion of the summand indexed by a point `x` of the geometric fibre above `s` into
the direct sum of the stalks over that fibre. -/
public def fiberStalkOf (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v})
    (x : GeometricFiberPoint B f s) :
    etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj ⟶
      AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) :=
  let := Classical.decEq (GeometricFiberPoint B f s)
  AddCommGrpCat.ofHom (DirectSum.of (fun y : GeometricFiberPoint B f s =>
    ↑(etaleStalk B X.obj X.property (y.toGeometricPoint B f s) F.obj)) x)

/-- Two maps out of the direct sum of the stalks over the geometric fibre agree as soon as they
agree on every summand. -/
public theorem fiberStalks_hom_ext (s : GeometricPoint Y.obj)
    {F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}}
    {M : AddCommGrpCat.{max (u + 1) v}}
    {g h : AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s F) ⟶ M}
    (H : ∀ (x : GeometricFiberPoint B f s)
      (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s) F.obj)),
      g (fiberStalkOf.{u, v} B f s F x z) = h (fiberStalkOf.{u, v} B f s F x z)) :
    g = h := by
  let _inst : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact AddCommGrpCat.hom_ext (DirectSum.addHom_ext fun x z => H x z)

/-- The summand of the weighted sum over the geometric fibre indexed by a point `x` of the
fibre: the weight of `x` times the identification of the stalk of `f^{-1}F` at `x` with the
stalk of `F` at the geometric point below. -/
public def weightedTraceStalkSummand (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s) :
    ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
        ((abPullback.{u, v} B f).obj F).obj) →+
      ↑(etaleStalk B Y.obj Y.property s F.obj) :=
  AddMonoidHom.mk'
    (fun z => w (x.1 default) • (fiberPointPullbackStalkIso.{u, v} B f s F x).hom z)
    (fun a b => by rw [map_add, smul_add])

/-- The summand indexed by `x` sends `z` to the weight of `x` times the image of `z` under the
identification of the stalk of `f^{-1}F` at `x` with the stalk of `F` at `s`. -/
@[simp]
public theorem weightedTraceStalkSummand_apply (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      ((abPullback.{u, v} B f).obj F).obj)) :
    weightedTraceStalkSummand.{u, v} B f w F s x z =
      w (x.1 default) • (fiberPointPullbackStalkIso.{u, v} B f s F x).hom z :=
  rfl

end FiberPoint

section WeightedTrace

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **The fibre integral on a geometric stalk.** The weighted sum over the geometric fibre of
`f` above a geometric point `s` of `Y`, as a map out of the direct sum of stalks which the
decomposition of Stacks 0F5F identifies with the stalk of `f_! f^{-1}F` at `s`: the summand
indexed by a point `x` of the fibre is multiplied by the weight of `x` and carried to the stalk
of `F` at `s`. -/
public def weightedTraceStalkMap (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) :
    AddCommGrpCat.of (fiberStalks.{u, max (u + 1) v} B f s
        ((abPullback.{u, v} B f).obj F)) ⟶
      etaleStalk B Y.obj Y.property s F.obj :=
  let := Classical.decEq (GeometricFiberPoint B f s)
  AddCommGrpCat.ofHom
    (DirectSum.toAddMonoid (weightedTraceStalkSummand.{u, v} B f w F s))

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The weighted sum over the geometric fibre, on the summand indexed by a point `x` of the
fibre: the weight of `x` times the identification of the stalk of `f^{-1}F` at `x` with the
stalk of `F` at `s`. -/
public theorem weightedTraceStalkMap_fiberStalkOf (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      ((abPullback.{u, v} B f).obj F).obj)) :
    weightedTraceStalkMap.{u, v} B f w F s
        (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z) =
      w (x.1 default) • (fiberPointPullbackStalkIso.{u, v} B f s F x).hom z := by
  let _inst : DecidableEq (GeometricFiberPoint B f s) := Classical.decEq _
  exact DirectSum.toAddMonoid_of (weightedTraceStalkSummand.{u, v} B f w F s) x z

/-- **The characterising property of the trace map of Stacks 0GKG.** A morphism
`τ : f_! f^{-1}F ⟶ F` has weighted trace stalks if at every geometric point `s` of `Y` the map
it induces on stalks, read through the decomposition of the stalk of `f_! f^{-1}F` at `s` into
the direct sum of the stalks of `f^{-1}F` over the geometric fibre above `s`, is the weighted
sum over that fibre. -/
public def HasWeightedTraceStalks (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F) : Prop :=
  ∀ s : GeometricPoint Y.obj,
    (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).inv ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op τ.1) =
      weightedTraceStalkMap.{u, v} B f w F s

/-- The summandwise reading of the characterising property: the trace carries a germ of
`f^{-1}F` at a point `x` of the geometric fibre above `s`, placed in the summand of the stalk
decomposition indexed by `x`, to the weight of `x` times the corresponding germ of `F` at `s`. -/
public theorem hasWeightedTraceStalks_fiberStalkOf (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    {τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F}
    (h : HasWeightedTraceStalks.{u, v} B f w F τ)
    (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (z : ↑(etaleStalk B X.obj X.property (x.toGeometricPoint B f s)
      ((abPullback.{u, v} B f).obj F).obj)) :
    (colim.map (Functor.whiskerLeft
        (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op τ.1))
      ((fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).inv
        (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z)) =
      w (x.1 default) • (fiberPointPullbackStalkIso.{u, v} B f s F x).hom z :=
  (ConcreteCategory.congr_hom (h s)
      (fiberStalkOf.{u, v} B f s ((abPullback.{u, v} B f).obj F) x z)).trans
    (weightedTraceStalkMap_fiberStalkOf.{u, v} B f w F s x z)

/-- **Uniqueness of the weighted trace map of Stacks 0GKG.** Two morphisms
`f_! f^{-1}F ⟶ F` whose effect on every geometric stalk is the weighted sum over the geometric
fibre are equal.

The geometric stalk functors are jointly faithful on abelian étale sheaves, so it is enough that
the two maps induced on the stalk at every geometric point agree; the prescribed effect fixes
each of those maps, the decomposition of Stacks 0F5F being an isomorphism. No hypothesis on `w`
enters: uniqueness holds for an arbitrary integer-valued function on `X`. -/
public theorem hasWeightedTraceStalks_unique (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    {τ τ' : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F}
    (h : HasWeightedTraceStalks.{u, v} B f w F τ)
    (h' : HasWeightedTraceStalks.{u, v} B f w F τ') :
    τ = τ' := by
  refine (jointlyFaithful_etaleStalkSheafFiber.{u, v} B Y.obj Y.property).map_injective
    fun s => ?_
  exact (Iso.cancel_iso_inv_left
    (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)) _ _).1
    ((h s).trans (h' s).symm)

/-- There is at most one morphism `f_! f^{-1}F ⟶ F` with the weighted trace behaviour on
geometric stalks. -/
public theorem subsingleton_hasWeightedTraceStalks (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    Subsingleton {τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F //
      HasWeightedTraceStalks.{u, v} B f w F τ} :=
  ⟨fun τ τ' => Subtype.ext (hasWeightedTraceStalks_unique.{u, v} B f w F τ.2 τ'.2)⟩

/-- **The characterising property of the trace map at the level of the finite-support direct
image presheaf.** A morphism of presheaves `σ : f_{p!} f^{-1}F ⟶ F` has weighted trace stalks if
at every geometric point `s` of `Y` the map it induces on stalks, read through the germ
decomposition of Stacks 0F6P of the stalk of `f_{p!} f^{-1}F` at `s`, is the weighted sum over
the geometric fibre above `s`. -/
public def HasWeightedTracePresheafStalks (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (σ : (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
      ((abPullback.{u, v} B f).obj F) ⟶ F.obj) : Prop :=
  ∀ s : GeometricPoint Y.obj,
    (finiteSupportStalkIso.{u, max (u + 1) v} B f s ((abPullback.{u, v} B f).obj F)
          (fun _ => inferInstance)).inv ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op σ) =
      weightedTraceStalkMap.{u, v} B f w F s

/-- The stalk map of a morphism out of `f_! f^{-1}F`, read through the stalk decomposition of
Stacks 0F5F, is the stalk map of the morphism of presheaves it restricts to along the
sheafification unit, read through the germ decomposition of Stacks 0F6P: sheafification does not
change a stalk, and the decomposition of Stacks 0F5F is by definition the germ decomposition
composed with that invariance. -/
public theorem finiteSupportStalkIso_inv_comp_stalkMap_toSheafify
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F)
    (s : GeometricPoint Y.obj) :
    (finiteSupportStalkIso.{u, max (u + 1) v} B f s ((abPullback.{u, v} B f).obj F)
          (fun _ => inferInstance)).inv ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
          (toSheafify (SmallEtale.topology B Y.obj Y.property)
            ((finiteSupportPushforward.{u, max (u + 1) v} B f
              (fun _ => inferInstance)).1.obj ((abPullback.{u, v} B f).obj F)) ≫ τ.1)) =
      (fShriekStalkIso.{u, v} B f s ((abPullback.{u, v} B f).obj F)).inv ≫
        colim.map (Functor.whiskerLeft
          (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op τ.1) :=
  (congrArg
    (fun m => (finiteSupportStalkIso.{u, max (u + 1) v} B f s
      ((abPullback.{u, v} B f).obj F) (fun _ => inferInstance)).inv ≫ m)
    ((etaleStalkPresheafFunctor B Y.obj Y.property s AddCommGrpCat.{max (u + 1) v}).map_comp
      (toSheafify (SmallEtale.topology B Y.obj Y.property)
        ((finiteSupportPushforward.{u, max (u + 1) v} B f
          (fun _ => inferInstance)).1.obj ((abPullback.{u, v} B f).obj F))) τ.1)).trans
    (Category.assoc _ _ _).symm

/-- A morphism `f_! f^{-1}F ⟶ F` has the weighted trace behaviour on geometric stalks exactly
when the morphism of presheaves it restricts to along the sheafification unit does. -/
public theorem hasWeightedTraceStalks_iff_presheaf (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F) :
    HasWeightedTraceStalks.{u, v} B f w F τ ↔
      HasWeightedTracePresheafStalks.{u, v} B f w F
        (toSheafify (SmallEtale.topology B Y.obj Y.property)
          ((finiteSupportPushforward.{u, max (u + 1) v} B f
            (fun _ => inferInstance)).1.obj ((abPullback.{u, v} B f).obj F)) ≫ τ.1) := by
  constructor
  · intro h s
    exact (finiteSupportStalkIso_inv_comp_stalkMap_toSheafify.{u, v} B f F τ s).trans (h s)
  · intro h s
    exact (finiteSupportStalkIso_inv_comp_stalkMap_toSheafify.{u, v} B f F τ s).symm.trans (h s)

/-- **The trace map exists exactly when it exists on the finite-support direct image presheaf.**
`f_! f^{-1}F` is the sheafification of `f_{p!} f^{-1}F` and `F` is a sheaf, so a morphism
`f_! f^{-1}F ⟶ F` is the same thing as a morphism of presheaves `f_{p!} f^{-1}F ⟶ F`, and the
characterisation on geometric stalks matches up under that bijection.

This is the reduction of the existence half of Stacks 0GKG to a construction on sections: it
says exactly which object a construction has to produce.  That construction is carried out in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.IntegralTracePresheaf` for the
constant sheaf, and transported to a general `F` through the projection formula of Stacks
0GKF. -/
public theorem exists_hasWeightedTraceStalks_iff_presheaf (w : X.obj → ℤ)
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    (∃ τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F,
        HasWeightedTraceStalks.{u, v} B f w F τ) ↔
      ∃ σ : (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj
          ((abPullback.{u, v} B f).obj F) ⟶ F.obj,
        HasWeightedTracePresheafStalks.{u, v} B f w F σ := by
  refine ⟨fun ⟨τ, hτ⟩ => ⟨_, (hasWeightedTraceStalks_iff_presheaf.{u, v} B f w F τ).1 hτ⟩,
    fun ⟨σ, hσ⟩ => ⟨⟨sheafifyLift (SmallEtale.topology B Y.obj Y.property) σ F.property⟩,
      (hasWeightedTraceStalks_iff_presheaf.{u, v} B f w F _).2 (by rwa [toSheafify_sheafifyLift])⟩⟩

/- **No `@[stacks 0GKG]` attribute in this file.**  Stacks 0GKG asserts the existence *and* the
uniqueness of a trace map with the behaviour on geometric stalks above.  What is proved here is
uniqueness, together with the construction of the weighted sum on stalks which the
characterisation refers to, and the reduction of existence to a construction on sections.  The
whole claim -- both halves at the tag's hypotheses -- is
`AlgebraicGeometry.SmallEtale.existsUnique_hasWeightedTraceStalks` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceExistence`, and that
is where the attribute sits.  An attribute on a half of the statement would make the tag read as
proved while the other half was elsewhere.  The one case in which the trace map itself is
produced below is the zero weighting, which is degenerate and does not cover the tag either.
The other `0GKG` attributes in the development are all explicitly scoped: the étale trace map in
`...WeightedTrace.EtaleTraceCounit`, the fibre integral for an étale morphism in
`...WeightedTrace.EtaleCanonicalWeighting`, and the fibre integral for a general locally
quasi-finite morphism and a general weighting in `...WeightedTrace.FibreIntegral`. -/
omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- For the zero weighting the weighted sum over the geometric fibre is the zero map. -/
public theorem weightedTraceStalkMap_zero
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v})
    (s : GeometricPoint Y.obj) :
    weightedTraceStalkMap.{u, v} B f (fun _ => (0 : ℤ)) F s = 0 := by
  refine fiberStalks_hom_ext.{u, v} B f s fun x z => ?_
  rw [weightedTraceStalkMap_fiberStalkOf.{u, v} B f (fun _ => (0 : ℤ)) F s x z, zero_smul]
  simp

/-- The zero morphism has the weighted trace behaviour on geometric stalks for the zero
weighting. -/
public theorem hasWeightedTraceStalks_zero
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    HasWeightedTraceStalks.{u, v} B f (fun _ => (0 : ℤ)) F 0 := by
  intro s
  have hz : colim.map (Functor.whiskerLeft
      (Functor.Elements.π (geometricPointFiber B Y.obj Y.property s)).op
      (0 : ((fShriekFunctor.{u, v} B f).obj
        ((abPullback.{u, v} B f).obj F)).obj ⟶ F.obj)) = 0 := by
    refine colimit.hom_ext fun j => ?_
    simp
  rw [weightedTraceStalkMap_zero.{u, v} B f F s,
    show (0 : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F).1 =
      (0 : ((fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F)).obj ⟶ F.obj) from rfl,
    hz]
  exact comp_zero

/-- **The trace map for the zero weighting.** For the zero weighting — a weighting of every
morphism, by `AlgebraicGeometry.isWeighting_zero` — there is a unique morphism
`f_! f^{-1}F ⟶ F` with the weighted trace behaviour on geometric stalks, namely the zero
morphism. This is the degenerate case of Stacks 0GKG; it is recorded to show that the
characterisation is satisfiable. -/
public theorem existsUnique_hasWeightedTraceStalks_zero
    (F : Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}) :
    ∃! τ : (fShriekFunctor.{u, v} B f).obj ((abPullback.{u, v} B f).obj F) ⟶ F,
      HasWeightedTraceStalks.{u, v} B f (fun _ => (0 : ℤ)) F τ :=
  ⟨0, hasWeightedTraceStalks_zero.{u, v} B f F, fun _ hτ =>
    hasWeightedTraceStalks_unique.{u, v} B f (fun _ => (0 : ℤ)) F hτ
      (hasWeightedTraceStalks_zero.{u, v} B f F)⟩

end WeightedTrace

end SmallEtale

end AlgebraicGeometry

end
