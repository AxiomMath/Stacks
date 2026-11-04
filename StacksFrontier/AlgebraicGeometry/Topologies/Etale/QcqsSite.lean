module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.SchemePropertiesPermanence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# The small quasi-compact quasi-separated étale site of a scheme

Let `B` be a big étale site containing a scheme `S`. Besides the small étale site of `S` and its
affine full subcategory (Tag 021B, parts (2) and (4)), the objects of the small étale site whose
underlying scheme is quasi-compact and quasi-separated form a full subcategory, and the standard
étale coverings make it a site.

The point of this subsite is the object it contains that the affine one does not: `S / S` itself.
`AlgebraicGeometry.SmallAffineEtale.final` needs `[IsAffine S]`, and that single hypothesis is
where the affineness in the registered affine case of [Stacks, Tag 03Q6] comes from — a
quasi-compact quasi-separated `S` is *not* an object of its own small affine étale site, so the
cohomology of `S` is not the cohomology over an object of that site, while on the subsite here it
is. Quasi-compactness and quasi-separatedness of `S` are exactly the hypotheses
[Stacks, Tag 09YQ] puts on the levels of its system, so this is the subsite at which that
theorem's levels are objects of their own sites.

## Main definitions

* `AlgebraicGeometry.qcqsCreatesPullbacks` — the quasi-compact quasi-separated objects of a
  category over `Scheme` create fibre products, as soon as the functor to schemes preserves them.
  This is the counterpart of `AlgebraicGeometry.affineCreatesPullbacks`, and its
  scheme-theoretic input is `AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_pullback`.
* `AlgebraicGeometry.SmallEtale.IsQcqs` — the property of a small étale object over `S` that its
  underlying scheme is quasi-compact and quasi-separated.
* `AlgebraicGeometry.SmallQcqsEtale` — the resulting full subcategory, with
  `AlgebraicGeometry.SmallQcqsEtale.inclusion` into the small étale category and
  `AlgebraicGeometry.SmallQcqsEtale.toScheme` to schemes.
* `AlgebraicGeometry.SmallQcqsEtale.IsCovering`, `.precoverage`, `.topology` — the finite étale
  coverings, as a precoverage and the topology it generates. Finiteness is kept, exactly as in
  `AlgebraicGeometry.SmallAffineEtale.IsCovering`, because that is what the colimit-of-sites
  theorem [Stacks, Tag 09YL] consumes.
* `AlgebraicGeometry.SmallQcqsEtale.final` — the object `S / S`, available whenever `S` is
  quasi-compact and quasi-separated.
* `AlgebraicGeometry.SmallAffineEtale.toQcqsEtale` — the factorisation of the affine subsite
  through this one.

## Main results

* `AlgebraicGeometry.SmallQcqsEtale.finalIsTerminal`,
  `AlgebraicGeometry.hasTerminal_smallQcqsEtale`,
  `AlgebraicGeometry.hasFiniteLimits_smallQcqsEtale` — **a terminal object with no affineness
  hypothesis**, and hence finite limits, for a quasi-compact quasi-separated `S`.
* `AlgebraicGeometry.hasPullbacks_smallQcqsEtale` and the two `preservesPullbacks_*` instances.
* `AlgebraicGeometry.SmallAffineEtale.toQcqsEtale_comp_inclusion` — the factorisation is strict:
  the affine inclusion into the small étale category *equals* this factorisation followed by the
  inclusion of the quasi-compact quasi-separated subsite.

## Implementation notes

An object of `SmallQcqsEtale` carries its quasi-compactness and quasi-separatedness as a
conjunction of the two type classes rather than as a `MorphismProperty` of the structure
morphism: the two conditions wanted are conditions on the *scheme*, and the fibre-product and
terminal-object arguments use them in that form. The two projections are registered as instances,
so an object of the subsite supplies them to instance search.

No `@[stacks]` attribute appears in this file. The Stacks Project considers the small étale site
and its *affine* full subcategory (Tag 021B, parts (2) and (4)) and proves fibre products and the
final object for those (Tag 021D); it does not consider the quasi-compact quasi-separated
subcategory, so nothing here is a statement the source makes and nothing here is registered
against a tag. The same choice, for the same reason, is made in
`StacksFrontier/AlgebraicGeometry/Topologies/Etale/SmallEtaleFiniteLimits.lean`.

`qcqsCreatesPullbacks` is where the stability enters. The fibre product of quasi-compact
quasi-separated schemes over a quasi-compact quasi-separated scheme is again one, which is
`AlgebraicGeometry.compactSpace_and_quasiSeparatedSpace_pullback` ([Stacks, Tag 0816] (3)); what
remains is to carry that along the comparison isomorphism
`CategoryTheory.Limits.PreservesPullback.iso`, which is done with
`AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace` and
`AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated`, an isomorphism of schemes being both
quasi-compact and quasi-separated.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 021D](https://stacks.math.columbia.edu/tag/021D)
* [Stacks Project, Tag 0816](https://stacks.math.columbia.edu/tag/0816)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u' u

namespace AlgebraicGeometry

/-! ### Fibre products in a quasi-compact quasi-separated full subcategory -/

/-- **The quasi-compact quasi-separated objects of a category over `Scheme` create fibre
products**, as soon as the functor to schemes preserves them. This is the counterpart, for the
quasi-compact quasi-separated condition, of `AlgebraicGeometry.affineCreatesPullbacks`. -/
@[instance_reducible]
public noncomputable def qcqsCreatesPullbacks
    {C : Type u'} [Category.{v, u'} C] [HasPullbacks C]
    (G : C ⥤ Scheme.{u}) [PreservesLimitsOfShape WalkingCospan G] :
    CreatesLimitsOfShape WalkingCospan
      (ObjectProperty.ι
        (fun X : C => CompactSpace (G.obj X) ∧ QuasiSeparatedSpace (G.obj X))) where
  CreatesLimit := fun {F} => by
    let D := F ⋙ ObjectProperty.ι
      (fun X : C => CompactSpace (G.obj X) ∧ QuasiSeparatedSpace (G.obj X))
    have hl := (F.obj .left).property
    have hr := (F.obj .right).property
    have ho := (F.obj .one).property
    have : CompactSpace (G.obj (D.obj .left)) := hl.1
    have : QuasiSeparatedSpace (G.obj (D.obj .left)) := hl.2
    have : CompactSpace (G.obj (D.obj .right)) := hr.1
    have : QuasiSeparatedSpace (G.obj (D.obj .right)) := hr.2
    have : CompactSpace (G.obj (D.obj .one)) := ho.1
    have : QuasiSeparatedSpace (G.obj (D.obj .one)) := ho.2
    let t := pullback.cone (D.map WalkingCospan.Hom.inl) (D.map WalkingCospan.Hom.inr)
    refine createsLimitFullSubcategoryInclusion' F
      ((IsLimit.postcomposeInvEquiv (diagramIsoCospan D) t).symm (limit.isLimit _)) ?_
    let e := PreservesPullback.iso G (D.map WalkingCospan.Hom.inl)
      (D.map WalkingCospan.Hom.inr)
    obtain ⟨_, _⟩ := compactSpace_and_quasiSeparatedSpace_pullback
      (G.map (D.map WalkingCospan.Hom.inl)) (G.map (D.map WalkingCospan.Hom.inr))
    exact ⟨QuasiCompact.compactSpace_of_compactSpace e.hom,
      quasiSeparatedSpace_of_quasiSeparated e.hom⟩

/-! ### The site -/

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The property of a small étale object over `S` that its underlying scheme is quasi-compact
and quasi-separated. -/
public abbrev SmallEtale.IsQcqs : ObjectProperty (SmallEtale B S hS) :=
  fun X ↦ CompactSpace ((SmallEtale.toScheme B S hS).obj X) ∧
    QuasiSeparatedSpace ((SmallEtale.toScheme B S hS).obj X)

/-- The small quasi-compact quasi-separated étale category of `S`: the full subcategory of the
small étale category on the objects whose underlying scheme is quasi-compact and
quasi-separated. -/
public abbrev SmallQcqsEtale := (SmallEtale.IsQcqs B S hS).FullSubcategory

namespace SmallQcqsEtale

/-- The canonical full embedding into the small étale category. -/
public abbrev inclusion : SmallQcqsEtale B S hS ⥤ SmallEtale B S hS :=
  (SmallEtale.IsQcqs B S hS).ι

/-- The canonical functor to schemes. -/
public abbrev toScheme : SmallQcqsEtale B S hS ⥤ Scheme.{u} :=
  inclusion B S hS ⋙ SmallEtale.toScheme B S hS

/-- Every object of the small quasi-compact quasi-separated étale category has quasi-compact
underlying scheme. -/
public instance compactSpace_toScheme_obj (X : SmallQcqsEtale B S hS) :
    CompactSpace ((toScheme B S hS).obj X) :=
  X.property.1

/-- Every object of the small quasi-compact quasi-separated étale category has quasi-separated
underlying scheme. -/
public instance quasiSeparatedSpace_toScheme_obj (X : SmallQcqsEtale B S hS) :
    QuasiSeparatedSpace ((toScheme B S hS).obj X) :=
  X.property.2

/-- A family in the small quasi-compact quasi-separated étale category is covering when its
image in the small étale category is covering and it is finite. Finiteness is kept for the same
reason as in `AlgebraicGeometry.SmallAffineEtale.IsCovering`: it is what the
colimit-of-sites theorem consumes. -/
public abbrev IsCovering (E : Covering (SmallQcqsEtale B S hS)) : Prop :=
  SmallEtale.IsCovering B S hS
      ⟨(inclusion B S hS).obj E.1, E.2.map (inclusion B S hS)⟩ ∧
    Finite E.2.I₀

/-- The precoverage presented by the finite étale covering families. -/
public def precoverage : Precoverage (SmallQcqsEtale B S hS) where
  coverings X := {R | ∃ E : PreZeroHypercover.{u + 1} X,
    R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩}

/-- A presieve belongs to the precoverage exactly when it is presented by a finite étale
covering family. -/
public theorem mem_precoverage_iff {X : SmallQcqsEtale B S hS} {R : Presieve X} :
    R ∈ precoverage B S hS X ↔ ∃ E : PreZeroHypercover.{u + 1} X,
      R = E.presieve₀ ∧ IsCovering B S hS ⟨X, E⟩ :=
  Iff.rfl

/-- The Grothendieck topology generated by the finite étale covering families. -/
public abbrev topology : GrothendieckTopology (SmallQcqsEtale B S hS) :=
  (precoverage B S hS).toGrothendieck

end SmallQcqsEtale

/-! ### Fibre products -/

private noncomputable instance createsPullbacks_smallQcqsEtale :
    CreatesLimitsOfShape WalkingCospan (SmallQcqsEtale.inclusion B S hS) :=
  qcqsCreatesPullbacks (SmallEtale.toScheme B S hS)

/-- The small quasi-compact quasi-separated étale category of `S` admits fibre products. -/
public instance hasPullbacks_smallQcqsEtale :
    HasPullbacks (SmallQcqsEtale B S hS) :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (SmallQcqsEtale.inclusion B S hS)

/-- The inclusion into the small étale category preserves fibre products. -/
public instance preservesPullbacks_smallQcqsEtaleInclusion :
    PreservesLimitsOfShape WalkingCospan (SmallQcqsEtale.inclusion B S hS) :=
  inferInstance

/-- The canonical functor to schemes preserves fibre products. -/
public instance preservesPullbacks_smallQcqsEtaleToScheme :
    PreservesLimitsOfShape WalkingCospan (SmallQcqsEtale.toScheme B S hS) := by
  apply comp_preservesLimitsOfShape

/-! ### The affine subsite factors through this one -/

/-- An affine scheme is quasi-compact and quasi-separated, so the small affine étale category of
`S` sits inside the small quasi-compact quasi-separated one. -/
public def SmallAffineEtale.toQcqsEtale :
    SmallAffineEtale B S hS ⥤ SmallQcqsEtale B S hS :=
  ObjectProperty.lift (SmallEtale.IsQcqs B S hS) (SmallAffineEtale.inclusion B S hS)
    (fun X => by
      have : IsAffine ((SmallEtale.toScheme B S hS).obj
          ((SmallAffineEtale.inclusion B S hS).obj X)) := X.property
      exact ⟨inferInstance, quasiSeparatedSpace_of_isAffine _⟩)

/-- **The factorisation is strict.** The inclusion of the small affine étale category into the
small étale category is the factorisation through the quasi-compact quasi-separated subsite
followed by that subsite's inclusion. -/
public theorem SmallAffineEtale.toQcqsEtale_comp_inclusion :
    SmallAffineEtale.toQcqsEtale B S hS ⋙ SmallQcqsEtale.inclusion B S hS =
      SmallAffineEtale.inclusion B S hS :=
  rfl

/-- On schemes the two routes out of the small affine étale category agree. -/
public theorem SmallAffineEtale.toQcqsEtale_comp_toScheme :
    SmallAffineEtale.toQcqsEtale B S hS ⋙ SmallQcqsEtale.toScheme B S hS =
      SmallAffineEtale.toScheme B S hS :=
  rfl

/-! ### The terminal object, with no affineness hypothesis -/

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- The object `S / S` of the small quasi-compact quasi-separated étale category. Only
quasi-compactness and quasi-separatedness of `S` are needed, not affineness: this is the object
that distinguishes this subsite from the small affine étale one. -/
public def SmallQcqsEtale.final : SmallQcqsEtale B S hS :=
  ⟨SmallEtale.final B S hS, ⟨inferInstanceAs (CompactSpace S), inferInstanceAs
    (QuasiSeparatedSpace S)⟩⟩

/-- **`S / S` is terminal in the small quasi-compact quasi-separated étale category of a
quasi-compact quasi-separated scheme `S`.** -/
public noncomputable def SmallQcqsEtale.finalIsTerminal :
    IsTerminal (SmallQcqsEtale.final B S hS) :=
  IsTerminal.ofUniqueHom
    (fun Y => (SmallQcqsEtale.inclusion B S hS).preimage
      ((SmallEtale.finalIsTerminal B S hS).from
        ((SmallQcqsEtale.inclusion B S hS).obj Y)))
    (fun _ _ => (SmallQcqsEtale.inclusion B S hS).map_injective
      ((SmallEtale.finalIsTerminal B S hS).hom_ext _ _))

/-- The small quasi-compact quasi-separated étale category of a quasi-compact quasi-separated
scheme has a terminal object. -/
public instance hasTerminal_smallQcqsEtale : HasTerminal (SmallQcqsEtale B S hS) :=
  (SmallQcqsEtale.finalIsTerminal B S hS).hasTerminal

/-- The small quasi-compact quasi-separated étale category of a quasi-compact quasi-separated
scheme has all finite limits. -/
public instance hasFiniteLimits_smallQcqsEtale : HasFiniteLimits (SmallQcqsEtale B S hS) :=
  hasFiniteLimits_of_hasTerminal_and_pullbacks

end AlgebraicGeometry

end
