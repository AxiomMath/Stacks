module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.KFlatPullbackEnoughPointsUnconditional
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.Topos

/-!
# Pullback of K-flat complexes along a morphism of sites, at a named point of the target

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi whose underlying functor
`u : C' ⥤ C` of the sites is a morphism of sites, and let `Φ` be a point of `C`.  The morphism
of sites gives a morphism of topoi `Sh(C) ⟶ Sh(C')` (Stacks 00XC), and composing it with the
point of the topos `Sh(C)` attached to `Φ` (Stacks 00YA part (1)) gives a point of the topos
`Sh(C')`, hence by Stacks 00YA part (2) a **point `Ψ` of the site `C'`** whose stalk functor is
the inverse image along `f` followed by the stalk at `Φ`.  That `Ψ` is the point the source
calls `q = f ∘ Φ`, and it is the point at which Stacks 05V5 computes the stalk of a module
pullback:

`(f^*M)_Φ ≅ M_Ψ ⊗_{O'_Ψ} O_Φ`.

With `Ψ` so named, the K-flatness assertion of Stacks 0DEP is the source's three-step
deduction: K-flatness of `f^*K` is tested at the points of `C` by part (2) of Stacks 0DEN,
which applies because `C` has a conservative family of points; at a point `Φ` the stalk complex
of `f^*K` is an extension of scalars of the stalk complex of `K` at `Ψ`, which is K-flat by
part (1) of Stacks 0DEN on the target; and extension of scalars preserves K-flatness, which is
Stacks 06Y1.

## Main definitions

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.toposPoint`: the point of the
  topos `Sh(C')` obtained by composing a point of `Sh(C)` with the morphism of topoi of `f`.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetPoint`: the point `Ψ` of
  the site `C'` underlying it.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.StalkBaseChange`: Stacks 05V5 at
  the level of complexes, stated at `Ψ` rather than at an unnamed point of the target.

## Main results

* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.targetPointStalkIso`: the stalk
  functor of `Ψ` is the inverse image along `f` followed by the stalk functor of `Φ`.
* `Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.pullbackStalkBaseChange`: the
  comparison at `Ψ` implies the comparison at an unnamed point of the target, so it is the
  stronger of the two hypotheses.
* `kFlat_pullbackComplex_of_morphismOfSites`, in the same namespace: the K-flatness assertion of
  Stacks 0DEP, granted Stacks 05V5 at the level of complexes at the named point `Ψ` and nothing
  else.

## Implementation notes

**Why the morphism-of-sites hypothesis is present, and why it is not a weakening.**  Stacks
0DEP is a statement about a morphism of ringed *topoi*.  A
`AlgebraicGeometry.RingedToposSiteHom` records only that its underlying functor `u` is
continuous, which does not make `u` induce a morphism of topoi at all: the inverse image on
sheaves need not be exact.  The hypothesis `u.IsMorphismOfSites` is exactly the missing
exactness, and it is what
`AlgebraicGeometry.RingedToposSiteHom.toToposHom` consumes to produce the morphism of topoi;
sibling results in this development carry it for the same reason, among them
`Stacks.Sheaves.DerivedPullback.KFlatPullback.kFlat_pullbackComplex` (Stacks 0G7E) and
`Stacks.Sheaves.DerivedPullback.hasLeftDerivedFunctor_pullbackOnHomotopy` (Stacks 06YY).

Without it the comparison of Stacks 05V5 is not merely unavailable but false.  A site with no
objects carries the trivial topology, for which every presheaf is a sheaf and hence every
functor out of that site is continuous; so there is a genuine `RingedToposSiteHom` from the
ringed point to the ringed topos on the empty site, and over it no point of the target site
exists, while the source site has one.  That refutation is
`not_pullbackStalkBaseChange_toPointlessTopos`, in the namespace
`Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints`, and it refutes even the weakest form
of the comparison, the one asking only that *some* point of the target carry it.  Naming `Ψ` as
the composite point, which is what the morphism-of-sites hypothesis makes possible, removes that
failure: the point is constructed rather than asserted to exist.

**What is quantified and what is named.**  `StalkBaseChange` names the point `Ψ` of the target
site and leaves the map of stalk rings `O'_Ψ ⟶ O_Φ` existentially quantified.  The asymmetry is
deliberate: the point is the datum whose existence fails without the morphism-of-sites
hypothesis, whereas no compatibility of the ring map with `f` is used downstream, Stacks 06Y1
preserving K-flatness along an arbitrary ring homomorphism.

**Where `StalkBaseChange` is inhabited.**
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.stalkBaseChange`, in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.StalkBaseChangeAtTheTargetPoint`,
constructs it, and Stacks 0DEP is tagged there.  The route is not the square of the two ringed
points: it is the factorization of the pullback of modules into the inverse image followed by
extension of scalars, Stacks 05V1 for sheaves of modules at the point `Ψ`, and the base-change
colimit interchange at a point of a site.

**Universes.**  Both ringed topoi are taken at `AlgebraicGeometry.RingedTopos.{u, u, u}`.  This
is forced independently by `SheafOfModules.pullback`, by both parts of Stacks 0DEN, and by
Stacks 00XC, whose two sites are small in the universe of the sheaves of sets; the smallness
side conditions of Stacks 00YA part (2) — `Small.{u} C'`, `LocallySmall.{u} C'` and
`HasSheafify C'.J (Type u)` — are then automatic.

## References

* [Stacks Project, Tag 0DEP](https://stacks.math.columbia.edu/tag/0DEP)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
* [Stacks Project, Tag 00XC](https://stacks.math.columbia.edu/tag/00XC)
* [Stacks Project, Tag 05V1](https://stacks.math.columbia.edu/tag/05V1)
* [Stacks Project, Tag 05V5](https://stacks.math.columbia.edu/tag/05V5)
* [Stacks Project, Tag 06Y1](https://stacks.math.columbia.edu/tag/06Y1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints

open Stacks.Sheaves.KFlatStalkCriterion (structureStalk stalkComplex)

noncomputable section

universe u

namespace Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites

/-! ### The point of the target site attached to a point of the source site -/

section TargetPoint

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  (f : AlgebraicGeometry.RingedToposSiteHom X Y) (hu : f.u.IsMorphismOfSites.{u} Y.J X.J)

/-- **The composite point of the target topos.**  A point of the topos `Sh(C)` composed with
the morphism of topoi `Sh(C) ⟶ Sh(C')` of Stacks 00XC attached to `f` is a point of the topos
`Sh(C')`.  This is the point the source writes `q = f ∘ Φ`. -/
def toposPoint (Φ : X.J.Point.{u}) : PointOfTopos.{u, u, u} Y.J :=
  MorphismOfTopoi.comp (f.toToposHom hu) Φ.pointOfTopos

/-- **The point `Ψ` of the target site.**  The point of the site `C'` underlying the composite
point of the topos `Sh(C')`, by Stacks 00YA part (2). -/
def targetPoint (Φ : X.J.Point.{u}) : Y.J.Point.{u} :=
  (toposPoint f hu Φ).sitePoint

/-- **The stalk functor at `Ψ` is the inverse image along `f` followed by the stalk functor at
`Φ`.**  This is the identification of Stacks 00YA part (2) for the composite point, and it is
the sheaf-of-sets shadow of the comparison of Stacks 05V5. -/
def targetPointStalkIso (Φ : X.J.Point.{u}) :
    (targetPoint f hu Φ).sheafFiber (A := Type u) ≅
      (f.toToposHom hu).inverseImage ⋙ Φ.sheafFiber (A := Type u) :=
  (toposPoint f hu Φ).sheafFiberIsoInverseImage

end TargetPoint

/-! ### Stacks 05V5 at the level of complexes, at the named point -/

section Pullback

variable {X Y : AlgebraicGeometry.RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : AlgebraicGeometry.RingedToposSiteHom X Y) (hu : f.u.IsMorphismOfSites.{u} Y.J X.J)

/-- **Stacks 05V5 at the level of complexes, at the composite point.**  For a point `Φ` of the
source site and a complex `K` of modules on the target, the stalk complex of the degreewise
pullback `f^*K` at `Φ` is an extension of scalars of the stalk complex of `K` at the point
`Ψ = f ∘ Φ` of the target site.

The point of the target is `targetPoint f hu Φ`, the one the source names; only the map of
stalk rings is left existentially quantified, Stacks 06Y1 using no compatibility of it
with `f`. -/
def StalkBaseChange : Prop :=
  ∀ (Φ : X.J.Point.{u})
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    ∃ φ : structureStalk Y.O (targetPoint f hu Φ) →+* structureStalk X.O Φ,
      Nonempty (stalkComplex X.O Φ ((KFlatPullback.pullbackComplex f).obj K) ≅
        (CochainComplex.extendScalars φ).obj (stalkComplex Y.O (targetPoint f hu Φ) K))

omit [HasWeakSheafify X.J AddCommGrpCat.{u}] [HasWeakSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The comparison at the named point is the stronger hypothesis.**  Naming the point of the
target site refines the existential form
`Stacks.Sheaves.DerivedPullback.KFlatPullbackEnoughPoints.PullbackStalkBaseChange`, which asks
only that some point of the target carry the comparison. -/
theorem pullbackStalkBaseChange (h : StalkBaseChange f hu) : PullbackStalkBaseChange f := by
  intro Φ K
  obtain ⟨φ, e⟩ := h Φ K
  exact ⟨targetPoint f hu Φ, φ, e⟩

/-! ### The K-flatness assertion of Stacks 0DEP -/

section Main

variable [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]

/-- **The K-flatness assertion of Stacks 0DEP, granted Stacks 05V5 at the named point and
nothing else.**  If the source site has a conservative family of points, the degreewise pullback
along `f` of a K-flat complex of `O_Y`-modules is a K-flat complex of `O_X`-modules.

The proof is the source's.  Part (2) of Stacks 0DEN tests K-flatness of `f^*K` at the points of
the source site, part (1) of Stacks 0DEN gives K-flatness of the stalk complexes of `K` on the
target, and Stacks 06Y1 carries that along the extension of scalars of `StalkBaseChange`.

No tag is placed here because `StalkBaseChange` is a hypothesis Stacks 0DEP does not have;
the tagged, unconditional form is
`Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites.kFlat_pullbackComplex`.  Unlike
the existential form it refines, this hypothesis is not refutable: the point of the target site
it speaks about is constructed from the morphism-of-sites hypothesis. -/
theorem kFlat_pullbackComplex_of_morphismOfSites (hX : X.J.HasConservativeFamily.{u})
    (h05V5 : StalkBaseChange f hu)
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Stacks.SheafOfModules.IsKFlat Y.O K) :
    Stacks.SheafOfModules.IsKFlat X.O ((KFlatPullback.pullbackComplex f).obj K) :=
  kFlat_pullbackComplex_of_enoughPoints f hX (pullbackStalkBaseChange f hu h05V5) K hK

end Main

end Pullback

end Stacks.Sheaves.DerivedPullback.KFlatPullbackMorphismOfSites

end

end
