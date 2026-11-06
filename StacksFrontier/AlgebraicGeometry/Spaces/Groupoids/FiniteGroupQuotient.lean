module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.Data.Fintype.Shrink
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelation
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Relations.PreRelations
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.FiniteCoproduct
public import StacksFrontier.CategoryTheory.Limits.BinaryProductDiagonal

/-!
# Graphs of automorphisms and coproducts of copies of a scheme over a base

The relation presenting the quotient of a scheme `U` over `S` by the action of a finite
group is the coproduct over the group of the graphs of the automorphisms. This file supplies
the two facts about that presentation which are independent of the action: a morphism
property passes from the diagonal of `U ⟶ S` to the underlying morphism of the graph of any
automorphism of `U` over `S`, and the underlying morphism of a map out of a coproduct of
copies of `U` in `CategoryTheory.Over S` is the descent of its restrictions to the summands.

## Main results

* `AlgebraicGeometry.Space.property_graph`: a morphism property which respects isomorphisms
  and holds for the diagonal of `U ⟶ S` holds for the underlying morphism of the graph of
  any automorphism of `U` over `S`. Its two instances are
  `AlgebraicGeometry.Space.isClosedImmersion_autGraph` for a separated `U ⟶ S` and
  `AlgebraicGeometry.Space.quasiCompact_graph` for a quasi-separated one.
* `AlgebraicGeometry.Space.property_left_of_sigmaDesc`: a morphism property respecting
  isomorphisms holds for the underlying morphism of a map out of a coproduct of copies of
  `U` as soon as it holds for the descent of its restrictions to the summands.
* `AlgebraicGeometry.Space.quasiCompact_sigmaDesc_of_finite`: a finite coproduct of
  quasi-compact morphisms with a common target is quasi-compact.

## Implementation notes

The graph of an automorphism `f` of `U` is `prod.lift f.hom (𝟙 U)`, the composite of the
diagonal of `U` with `prod.map f.hom (𝟙 U)`, which is an isomorphism. On underlying schemes
the diagonal of the binary product in `CategoryTheory.Over S` is the diagonal of `U ⟶ S`
composed with `CategoryTheory.Over.prodLeftIsoPullback`, so a property respecting
isomorphisms transfers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable {S : Scheme.{u}}

/-- A morphism property which respects isomorphisms and holds for the diagonal of `U ⟶ S`
holds for the underlying morphism of the graph `prod.lift f.hom (𝟙 U)` of an automorphism
`f` of `U` over `S`. -/
theorem property_graph (U : Over S) (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (hP : P (pullback.diagonal U.hom)) (f : Aut U) :
    P ((prod.lift f.asIso.hom (𝟙 U) : U ⟶ U ⨯ U).left) := by
  let d : U ⟶ U ⨯ U := prod.lift (𝟙 U) (𝟙 U)
  let p : (U ⨯ U).left ≅ pullback U.hom U.hom := Over.prodLeftIsoPullback U U
  have hfst : d.left ≫ p.hom ≫ pullback.fst U.hom U.hom = 𝟙 U.left := by
    rw [Over.prodLeftIsoPullback_hom_fst, ← Over.comp_left U (U ⨯ U) U d (prod.fst (X := U))]
    simp [d]
  have hsnd : d.left ≫ p.hom ≫ pullback.snd U.hom U.hom = 𝟙 U.left := by
    rw [Over.prodLeftIsoPullback_hom_snd, ← Over.comp_left U (U ⨯ U) U d (prod.snd (X := U))]
    simp [d]
  have heqDiag : d.left ≫ p.hom = pullback.diagonal U.hom :=
    pullback.hom_ext (by simpa using hfst) (by simpa using hsnd)
  let e : U ⨯ U ≅ U ⨯ U := prod.mapIso f.asIso (Iso.refl U)
  have heq : d ≫ e.hom = prod.lift f.asIso.hom (𝟙 U) := by
    rw [prod.mapIso_hom]
    apply prod.hom_ext <;> simp [d]
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  rw [← heq, Over.comp_left]
  exact MorphismProperty.RespectsIso.postcomp P e.hom.left d.left
    ((MorphismProperty.cancel_right_of_respectsIso P d.left p.hom).mp (heqDiag ▸ hP))

/-- The graph of an automorphism of a separated `S`-scheme is a closed immersion on
underlying schemes. -/
theorem isClosedImmersion_autGraph (U : Over S) [_root_.AlgebraicGeometry.IsSeparated U.hom]
    (f : Aut U) :
    _root_.AlgebraicGeometry.IsClosedImmersion
      ((prod.lift f.asIso.hom (𝟙 U) : U ⟶ U ⨯ U).left) :=
  property_graph U (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} :
    MorphismProperty Scheme.{u}) inferInstance f

/-- The graph of an automorphism of a quasi-separated `S`-scheme is quasi-compact on
underlying schemes. -/
theorem quasiCompact_graph (U : Over S) [QuasiSeparated U.hom] (f : Aut U) :
    QuasiCompact ((prod.lift f.asIso.hom (𝟙 U) : U ⟶ U ⨯ U).left) := by
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => inferInstance
  exact property_graph U (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) inferInstance f

/-- The coproduct inclusions of an `S`-scheme `U` are carried to the coproduct inclusions
of its underlying scheme. -/
@[reassoc (attr := simp)]
theorem left_ι_actionRelationUnderlyingIso (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (g : G) :
    (Sigma.ι (fun _ : G => U) g).left ≫ (actionRelationUnderlyingIso U G).hom =
      Sigma.ι (fun _ : G => U.left) g :=
  (((actionRelationUnderlyingIso U G).comp_inv_eq).mp
    (actionRelationUnderlyingIso_inv_ι U G g)).symm

/-- A morphism property respecting isomorphisms holds for the underlying morphism of a map
out of a coproduct of copies of `U` in `CategoryTheory.Over S`, indexed by a small type, as
soon as it holds for the descent of the restrictions to the summands over a shrunken index
type. -/
theorem property_left_of_sigmaDesc {U W : Over S} (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] (G : Type v) [Group G] [Small.{u} G] (j : (∐ fun _ : G => U) ⟶ W)
    (h : P (Sigma.desc fun i : Shrink.{u} G =>
      (Sigma.ι (fun _ : G => U) ((equivShrink.{u} G).symm i) ≫ j).left)) : P j.left := by
  classical
  set eG := equivShrink.{u} G
  set f : G → (U.left ⟶ W.left) := fun g => (Sigma.ι (fun _ : G => U) g ≫ j).left with hf
  let eSmall : (∐ fun _ : G => U.left) ≅ ∐ fun _ : Shrink.{u} G => U.left :=
    (Sigma.reindex eG.symm fun _ : G => U.left).symm
  have hι (g : G) : Sigma.ι (fun _ : G => U.left) g ≫ eSmall.hom =
      Sigma.ι (fun _ : Shrink.{u} G => U.left) (eG g) := by
    simpa [eSmall, Function.comp_def] using
      Sigma.ι_reindex_inv (f := fun _ : G => U.left) (ε := eG.symm) (eG g)
  have hdescSmall : eSmall.hom ≫ Sigma.desc (fun i => f (eG.symm i)) = Sigma.desc f := by
    refine Sigma.hom_ext _ _ fun g => ?_
    rw [← Category.assoc, hι g, Sigma.ι_desc, Sigma.ι_desc]
    simp [hf]
  have hleft : j.left = (actionRelationUnderlyingIso U G).hom ≫ Sigma.desc f := by
    refine (isColimitOfPreserves (Over.forget S)
      (colimit.isColimit (Discrete.functor fun _ : G => U))).hom_ext fun g => ?_
    show (Sigma.ι (fun _ : G => U) g.as).left ≫ j.left =
      ((Sigma.ι (fun _ : G => U) g.as).left ≫ (actionRelationUnderlyingIso U G).hom) ≫
        Sigma.desc f
    rw [left_ι_actionRelationUnderlyingIso, Sigma.ι_desc]
    simp [hf]
  rw [hleft, ← hdescSmall]
  exact MorphismProperty.RespectsIso.precomp P _ _
    (MorphismProperty.RespectsIso.precomp P _ _ h)

/-- A finite coproduct of quasi-compact morphisms with a common target is quasi-compact: the
preimage of an affine open is the union of the images of the finitely many preimages. -/
theorem quasiCompact_sigmaDesc_of_finite {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}}
    {T : Scheme.{u}} (f : ∀ i, Y i ⟶ T) (hf : ∀ i, QuasiCompact (f i)) :
    QuasiCompact (Sigma.desc f) := by
  refine quasiCompact_iff_forall_isAffineOpen.mpr fun W hW => ?_
  show IsCompact ((Sigma.desc f).base ⁻¹' (W : Set T))
  have hdecomp : ((Sigma.desc f).base ⁻¹' (W : Set T)) =
      ⋃ i, (Sigma.ι Y i).base '' ((f i).base ⁻¹' (W : Set T)) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk Y).surjective x
      rw [sigmaMk_mk]
      refine Set.mem_iUnion.mpr ⟨i, y, ?_, rfl⟩
      show (f i).base y ∈ W
      simpa [← Scheme.Hom.comp_apply] using hx
    · obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
      change (f i).base y ∈ W at hy
      simpa [← Scheme.Hom.comp_apply] using hy
  rw [hdecomp]
  exact isCompact_iUnion fun i =>
    ((quasiCompact_iff_forall_isAffineOpen.mp (hf i)) W hW).image
      (Scheme.Hom.continuous (Sigma.ι Y i))

/-- The restriction of the graph relation of a group action to the summand indexed by `g` is
the graph of the automorphism `g` acts by. -/
theorem ι_comp_actionRelation (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U) (g : G) :
    Sigma.ι (fun _ : G => U) g ≫ actionRelation U G a = prod.lift (a g).asIso.hom (𝟙 U) := by
  apply prod.hom_ext <;>
    simp [actionRelation, actionRelationTarget, actionRelationSource]

/-- The graph relation of a group action is a monomorphism when the stabilizers act
nontrivially on the residue fields they fix: it is then an étale equivalence relation. -/
theorem mono_actionRelation (U : Over S) (G : Type v) [Group G] [Small.{u} G]
    (a : G →* Aut U) (ha : ActsNontriviallyOnFixedResidueFields U G a) :
    Mono (actionRelation U G a) := by
  have := actionRelation_isEtaleEquivalenceRelation U G a ha
  exact ((Stacks.Groupoids.isEquivalenceRelation_iff_mono_and_isPreEquivalenceRelation
    (actionRelation U G a)).mp inferInstance).1

/-- The graph relation of a finite group acting on a scheme separated over
`S`, with stabilizers acting nontrivially on the residue fields they fix, is a closed
immersion: it is a finite monomorphism, being a finite coproduct of graphs of automorphisms
of a separated scheme. -/
@[sga "3 IX 2.4" "partial", sga "3 V 4.1" "special case"]
theorem isClosedImmersion_actionRelation (U : Over S) (G : Type v) [Group G] [Finite G]
    [Small.{u} G] (a : G →* Aut U) (ha : ActsNontriviallyOnFixedResidueFields U G a)
    [_root_.AlgebraicGeometry.IsSeparated U.hom] :
    _root_.AlgebraicGeometry.IsClosedImmersion (actionRelation U G a).left := by
  have : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => inferInstance
  have hfinite : _root_.AlgebraicGeometry.IsFinite (actionRelation U G a).left := by
    refine property_left_of_sigmaDesc
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) G _ ?_
    have (i : Shrink.{u} G) : _root_.AlgebraicGeometry.IsFinite ((Sigma.ι (fun _ : G => U)
        ((equivShrink.{u} G).symm i) ≫ actionRelation U G a).left) := by
      rw [ι_comp_actionRelation]
      exact ((_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).mp
        (isClosedImmersion_autGraph U (a ((equivShrink.{u} G).symm i)))).1
    infer_instance
  have : Mono (actionRelation U G a) := mono_actionRelation U G a ha
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono _).2
    ⟨hfinite, inferInstance⟩

/-- The graph relation of a finite group acting on a scheme quasi-separated
over `S` is quasi-compact: it is a finite coproduct of graphs of automorphisms of a
quasi-separated scheme. -/
theorem quasiCompact_actionRelation (U : Over S) (G : Type v) [Group G] [Finite G]
    [Small.{u} G] (a : G →* Aut U) [QuasiSeparated U.hom] :
    QuasiCompact (actionRelation U G a).left := by
  have : MorphismProperty.RespectsIso (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ _ _ => inferInstance
  refine property_left_of_sigmaDesc (@QuasiCompact.{u} : MorphismProperty Scheme.{u}) G _ ?_
  refine quasiCompact_sigmaDesc_of_finite _ fun i => ?_
  rw [ι_comp_actionRelation]
  exact quasiCompact_graph U (a ((equivShrink.{u} G).symm i))

end AlgebraicGeometry.Space

end
