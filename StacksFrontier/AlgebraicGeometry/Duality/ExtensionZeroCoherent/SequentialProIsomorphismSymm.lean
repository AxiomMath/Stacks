module

public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphism
import all StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SequentialProIsomorphism
public import Mathlib.CategoryTheory.Limits.FunctorToTypes
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ProCategoryOfMap
public import StacksFrontier.CategoryTheory.EssentiallyConstant.ProObject
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.StrictMajorant
public import StacksFrontier.Topology.Sheaves.Cohomology.InverseSystems.ProIsomorphismOfKernelSystems
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology

/-!
# Reversing a pro-isomorphism, and pro-isomorphisms as isomorphisms of pro-objects

A levelwise pro-isomorphism `InverseSequence.ProIso F G` of inverse sequences `F G : ℕᵒᵖ ⥤ 𝒟`
consists of increasing reindexings `α`, `β` and compatible morphisms `F_{α m} ⟶ G_m`,
`G_{β m} ⟶ F_m` whose two composites are transition morphisms. Such a pro-isomorphism can be
read in the other direction, and one between the images of two sequences under a fully faithful
functor comes from one between the sequences themselves.

The forward maps of a pro-isomorphism induce a transformation
`colim_n Mor(G_n, -) ⟶ colim_n Mor(F_n, -)` of functors of points, and the transformations
induced by the two directions are mutually inverse, because each composite acts on classes by a
transition morphism. So a levelwise pro-isomorphism is an isomorphism
`CategoryTheory.ProSeq.of F ≅ CategoryTheory.ProSeq.of G` in `Pro-𝒟`: the converse of
`CategoryTheory.ProSeq.proIsoOfIso`.

## Main definitions

* `InverseSequence.ProIso.symm`: a pro-isomorphism read in the other direction.
* `InverseSequence.ProIso.ofFullyFaithful`: a pro-isomorphism after a fully faithful functor is
  one before it.
* `CategoryTheory.Pro.seqHomColimMapOfProIso`: the transformation of functors of points induced
  by the forward maps of a pro-isomorphism.
* `CategoryTheory.ProSeq.isoOfProIso`: the isomorphism of pro-objects given by a levelwise
  pro-isomorphism.

## Main results

* `CategoryTheory.Pro.seqHomColimMapOfProIso_comp_symm`: the transformations induced by the two
  directions of a pro-isomorphism are mutually inverse.

## References

* [Stacks Project, Tag 05PX](https://stacks.math.columbia.edu/tag/05PX)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [-instance] CategoryTheory.Limits.instCategoryULiftHomULiftOfSmallCategory

universe v v' u u'

namespace CategoryTheory.Pro

variable {𝒟 : Type u} [Category.{v} 𝒟]

end CategoryTheory.Pro

namespace CategoryTheory.Pro

open CategoryTheory.Limits Opposite

end CategoryTheory.Pro

namespace CategoryTheory.ProSeq

open CategoryTheory.Limits Opposite

variable {𝒟 : Type u} [Category.{v} 𝒟]

end CategoryTheory.ProSeq

namespace InverseSequence.ProIso

variable {𝒟 : Type u} [Category.{v} 𝒟]

/-- A pro-isomorphism read in the other direction: the forward and backward maps, and the two
reindexings, are exchanged. -/
public def symm {F G : ℕᵒᵖ ⥤ 𝒟} (e : InverseSequence.ProIso F G) : InverseSequence.ProIso G F where
  α := e.β
  β := e.α
  αmono := e.βmono
  βmono := e.αmono
  αle := e.βle
  βle := e.αle
  φ := e.ψ
  ψ := e.φ
  φnat := e.ψnat
  ψnat := e.φnat
  ψφ := e.φψ
  φψ := e.ψφ

/-- A pro-isomorphism between the images of two inverse sequences under a fully faithful functor
is a pro-isomorphism between the sequences themselves: its levelwise maps have unique preimages,
and the equations they satisfy can be checked after applying the functor. -/
public def ofFullyFaithful {𝒞 : Type u'} [Category.{v'} 𝒞] {H : 𝒞 ⥤ 𝒟} (hH : H.FullyFaithful)
    {F G : ℕᵒᵖ ⥤ 𝒞} (e : InverseSequence.ProIso (F ⋙ H) (G ⋙ H)) :
    InverseSequence.ProIso F G where
  α := e.α
  β := e.β
  αmono := e.αmono
  βmono := e.βmono
  αle := e.αle
  βle := e.βle
  φ m := hH.preimage (e.φ m)
  ψ m := hH.preimage (e.ψ m)
  φnat h := hH.map_injective (by
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]; exact e.φnat h)
  ψnat h := hH.map_injective (by
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]; exact e.ψnat h)
  ψφ m := hH.map_injective (by
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]; exact e.ψφ m)
  φψ m := hH.map_injective (by
    simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]; exact e.φψ m)

end InverseSequence.ProIso

namespace CategoryTheory.Pro

open CategoryTheory.Limits Opposite

variable {𝒟 : Type u} [Category.{v} 𝒟]

/-- Precomposing the colimit leg of `colim_n Mor(F_n, -)` at a later stage with a transition
morphism gives the leg at the earlier stage. -/
public lemma coyoneda_map_tr_comp_ι (F : ℕᵒᵖ ⥤ 𝒟) {n m : ℕ} (h : n ≤ m) :
    coyoneda.map (InverseSequence.tr F h).op ≫ colimit.ι (F.op ⋙ coyoneda) (op (op m)) =
      colimit.ι (F.op ⋙ coyoneda) (op (op n)) :=
  colimit.w (F.op ⋙ coyoneda) (homOfLE h).op.op

/-- The transformation `colim_n Mor(G_n, -) ⟶ colim_n Mor(F_n, -)` of functors of points induced
by the forward maps `F_{α n} ⟶ G_n` of a pro-isomorphism: the class of `g : G_n ⟶ N` goes to the
class of `F_{α n} ⟶ G_n ⟶ N`. -/
public def seqHomColimMapOfProIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : InverseSequence.ProIso F G) :
    seqHomColim G ⟶ seqHomColim F :=
  colimit.desc (G.op ⋙ coyoneda)
    { pt := seqHomColim F
      ι :=
        { app := fun n => coyoneda.map (e.φ n.unop.unop).op ≫
            colimit.ι (F.op ⋙ coyoneda) (op (op (e.α n.unop.unop)))
          naturality := by
            rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ f
            have h : n ≤ m := leOfHom f.unop.unop
            obtain rfl : f = (homOfLE h).op.op := Subsingleton.elim _ _
            change coyoneda.map (InverseSequence.tr G h).op ≫ coyoneda.map (e.φ m).op ≫
                colimit.ι (F.op ⋙ coyoneda) (op (op (e.α m))) =
              (coyoneda.map (e.φ n).op ≫ colimit.ι (F.op ⋙ coyoneda) (op (op (e.α n)))) ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, ← coyoneda.map_comp, ← op_comp, ← e.φnat h,
              op_comp, coyoneda.map_comp, Category.assoc, coyoneda_map_tr_comp_ι] } }

/-- The leg of `Pro.seqHomColimMapOfProIso` at a stage `n`. -/
public lemma ι_seqHomColimMapOfProIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : InverseSequence.ProIso F G) (n : ℕ) :
    colimit.ι (G.op ⋙ coyoneda) (op (op n)) ≫ seqHomColimMapOfProIso e =
      coyoneda.map (e.φ n).op ≫ colimit.ι (F.op ⋙ coyoneda) (op (op (e.α n))) :=
  colimit.ι_desc _ _

/-- The transformations of functors of points induced by the two directions of a
pro-isomorphism are mutually inverse: backward after forward is a transition morphism, whose
effect on classes is trivial. -/
public lemma seqHomColimMapOfProIso_comp_symm {F G : ℕᵒᵖ ⥤ 𝒟} (e : InverseSequence.ProIso F G) :
    seqHomColimMapOfProIso e ≫ seqHomColimMapOfProIso e.symm = 𝟙 (seqHomColim G) := by
  refine colimit.hom_ext fun n => ?_
  obtain ⟨⟨n⟩⟩ := n
  rw [← Category.assoc, ι_seqHomColimMapOfProIso, Category.assoc, ι_seqHomColimMapOfProIso,
    ← Category.assoc, ← coyoneda.map_comp, ← op_comp, Category.comp_id]
  show coyoneda.map (e.ψ (e.α n) ≫ e.φ n).op ≫ _ = _
  rw [e.φψ n]
  exact coyoneda_map_tr_comp_ι G _

end CategoryTheory.Pro

namespace CategoryTheory.ProSeq

open CategoryTheory.Limits Opposite

variable {𝒟 : Type u} [Category.{v} 𝒟]

/-- A levelwise pro-isomorphism of inverse sequences is an isomorphism of the pro-objects they
determine. This is the converse of `CategoryTheory.ProSeq.proIsoOfIso`. -/
public def isoOfProIso {F G : ℕᵒᵖ ⥤ 𝒟} (e : InverseSequence.ProIso F G) :
    ProSeq.of F ≅ ProSeq.of G :=
  isoOfSeqHomColimIso
    { hom := Pro.seqHomColimMapOfProIso e.symm
      inv := Pro.seqHomColimMapOfProIso e
      hom_inv_id := Pro.seqHomColimMapOfProIso_comp_symm e.symm
      inv_hom_id := Pro.seqHomColimMapOfProIso_comp_symm e }

end CategoryTheory.ProSeq

end
