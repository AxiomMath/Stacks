module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EtaleEffectiveAlongProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.EtaleSpaceDescentEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.EtaleSpaceHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairGlobalFunctionsEqualizer
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentProperSurjective

/-!
# Stacks 0AGG from descent of spaces-étale sheaves along proper surjections

The proof of Stacks 0AGG in this library,
`AlgebraicGeometry.Space.properKernelPairCoequalizers`, rests on one input,
`AlgebraicGeometry.Space.EtaleSpaceDescentAlongProperSurjective`: étale descent of algebraic
spaces along a proper surjective morphism `f : Y ⟶ X`, in the fibre form, as two halves.

* Effectivity: every descent datum relative to `f` whose underlying space is étale over `Y` is
  isomorphic to the fibre descent datum `Y ×_X V` of an algebraic space `V` étale over `X`.
  This is Stacks 0GG0, which the library states in the canonical form
  (`AlgebraicGeometry.Space.isEffective_homDescentData_of_isEtale_of_isProper_isSurjective`)
  from the proper case of Stacks 0GFW and the translation
  `AlgebraicGeometry.Space.EtaleSpaceDescentEffectiveOfSheafDescent`. The canonical descent datum
  of `V` is the fibre descent datum (`AlgebraicGeometry.Space.canonicalIsoFibreDatum`), which
  turns the canonical form into the fibre form.
* Full faithfulness: morphisms of spaces étale over `X` are the morphisms of their fibre descent
  data, `AlgebraicGeometry.Space.etaleSpaceHomDescentAlongProperSurjective_of_descentEffective`,
  from the proper case of Stacks 0GFW alone.

So Stacks 0AGG follows from exactly two statements:
`AlgebraicGeometry.Space.DescentEffectiveAlongProperSurjective` (the proper case of Stacks 0GFW)
and `AlgebraicGeometry.Space.EtaleSpaceDescentEffectiveOfSheafDescent` (the translation step of
Stacks 0GG0). Both are theorems of the library:
`AlgebraicGeometry.Space.descentEffectiveAlongProperSurjective` and
`AlgebraicGeometry.Space.etaleSpaceDescentEffectiveOfSheafDescent`; so Stacks 0AGG is proved,
as `AlgebraicGeometry.Space.properKernelPairCoequalizers_holds`.

## Main results

* `AlgebraicGeometry.Space.canonicalIsoFibreDatum`: the canonical descent datum of an algebraic
  space over the target of a morphism is its fibre descent datum.
* `AlgebraicGeometry.Space.etaleSpaceDescentAlongProperSurjective_of_sheafDescent`: the input of
  the proof of Stacks 0AGG, from the two statements above.
* `AlgebraicGeometry.Space.properKernelPairCoequalizers_of_sheafDescent`: Stacks 0AGG, from the
  two statements above.
* `AlgebraicGeometry.Space.properKernelPairCoequalizers_holds`: **Stacks 0AGG**, proved, with no
  hypothesis.

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
* [Stacks Project, Tag 0ADQ](https://stacks.math.columbia.edu/tag/0ADQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Canonical

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
  (V : Descent.AlgebraicSpacesOver (B := B) (S := S) (hS := hS) X.obj)

/-- The comparison, chosen by the pullback functor on descent data, of the component of the
canonical descent datum of `V` relative to `f` with the fibre product `Y ×_X V`. -/
def canonicalComponentIso :
    ((Descent.canonicalDescentFunctor.{u, 0} f.hom X.property Y.property).obj V).obj
        PUnit.unit ≅ (fibreDatum f V).obj PUnit.unit :=
  Classical.choose (Descent.pullbackDescentDataFunctor.{u, 0, 0} (𝟙 X.obj) f.hom (𝟙 X.obj) f.hom
    (by simp) X.property X.property X.property Y.property).property
      ((Descent.trivialDescentFunctor.{u, 0} X.obj X.property).obj V)

/-- The move operation of the canonical descent datum does not change the point of `V`. -/
theorem canonicalComponentIso_move_fst {Z : Over X.obj}
    (v : Z ⟶ (Over.map f.hom).obj
      (((Descent.canonicalDescentFunctor.{u, 0} f.hom X.property Y.property).obj V).obj
        PUnit.unit))
    (y : Z ⟶ Over.mk f.hom) :
    (((Descent.canonicalDescentFunctor.{u, 0} f.hom X.property Y.property).obj V).transport.move
        (i := PUnit.unit) (j := PUnit.unit) v y).left ≫
        (canonicalComponentIso f V).hom.left ≫ pullback.fst V.obj.hom f.hom =
      v.left ≫ (canonicalComponentIso f V).hom.left ≫ pullback.fst V.obj.hom f.hom := by
  obtain ⟨q, r, hq, -, hglue⟩ := (Classical.choose_spec
    (Descent.pullbackDescentDataFunctor.{u, 0, 0} (𝟙 X.obj) f.hom (𝟙 X.obj) f.hom (by simp)
      X.property X.property X.property Y.property).property).2
        ((Descent.trivialDescentFunctor.{u, 0} X.obj X.property).obj V)
  have hq' : q.left = (canonicalComponentIso f V).hom.left ≫ pullback.fst V.obj.hom f.hom := hq
  dsimp only at hglue
  -- The gluing of the trivial datum is the symmetry, so it carries the second factor to the first.
  have hbr : (((Descent.trivialDescentFunctor.{u, 0} X.obj X.property).obj V).gluing PUnit.unit
      PUnit.unit).hom.left ≫ prod.snd = prod.fst :=
    prod.lift_snd _ _
  have e := congrArg (fun k => (Over.map (𝟙 X.obj)).map (prod.lift v y) ≫ k ≫ prod.snd) hglue
  simp only [Category.assoc, prod.lift_snd, prod.lift_fst, hbr] at e
  simp only [← Functor.map_comp_assoc, prod.lift_fst] at e
  have e' := congrArg (fun k => k.left) e
  simp only [Over.comp_left, Over.map_map_left] at e'
  rw [Descent.DescentData.transport_move, ← hq']
  exact e'

/-- The canonical descent datum of `V` relative to `f` (Stacks 0ADQ). -/
abbrev canonicalDatum : Descent.HomDescentData.{u, 0} f.hom X.property Y.property :=
  (Descent.canonicalDescentFunctor.{u, 0} f.hom X.property Y.property).obj V

/-- The comparison of components commutes with the move operations of the canonical and the
fibre descent data. -/
theorem canonicalComponentIso_move {Z : Over X.obj}
    (v : Z ⟶ (Over.map f.hom).obj ((canonicalDatum f V).obj PUnit.unit))
    (y : Z ⟶ Over.mk f.hom) :
    (canonicalDatum f V).transport.move (i := PUnit.unit) (j := PUnit.unit) v y ≫
        (Over.map f.hom).map (canonicalComponentIso f V).hom =
      (fibreDatum f V).transport.move (i := PUnit.unit) (j := PUnit.unit)
        (v ≫ (Over.map f.hom).map (canonicalComponentIso f V).hom) y := by
  refine Eq.trans ?_ (fibreDescentData_transport_move f (sheafOf f V)
    (v ≫ (Over.map f.hom).map (canonicalComponentIso f V).hom) y).symm
  have h₁ := Descent.fibreMove_left_fst (fun _ : PUnit.{1} => f.hom) V.obj (i := PUnit.unit)
    (j := PUnit.unit) (v ≫ (Over.map f.hom).map (canonicalComponentIso f V).hom) y
  have h₂ := Descent.fibreMove_left_snd (fun _ : PUnit.{1} => f.hom) V.obj (i := PUnit.unit)
    (j := PUnit.unit) (v ≫ (Over.map f.hom).map (canonicalComponentIso f V).hom) y
  have hw : (canonicalComponentIso f V).hom.left ≫ pullback.snd V.obj.hom f.hom =
      ((canonicalDatum f V).obj PUnit.unit).hom :=
    Over.w (canonicalComponentIso f V).hom
  have hb : ((canonicalDatum f V).transport.move (i := PUnit.unit) (j := PUnit.unit) v y).left ≫
      ((canonicalDatum f V).obj PUnit.unit).hom = y.left :=
    congrArg (fun k => k.left)
      ((canonicalDatum f V).transport.move_base (i := PUnit.unit) (j := PUnit.unit) v y)
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans <| (canonicalComponentIso_move_fst f V v y).trans <|
      (Category.assoc _ _ _).symm.trans h₁.symm
  · exact (Category.assoc _ _ _).trans <| (congrArg _ hw).trans <| hb.trans h₂.symm

/-- **The canonical descent datum is the fibre descent datum.** For an algebraic space `V` over
`X`, the canonical descent datum of `V` relative to `f : Y ⟶ X` (Stacks 0ADQ) is isomorphic to
the descent datum of the fibre product `Y ×_X V`. -/
def canonicalIsoFibreDatum :
    (canonicalDatum f V) ≅ fibreDatum f V := by
  refine Descent.DescentData.isoMk (fun _ => canonicalComponentIso f V) (fun i j => ?_)
  cases i
  cases j
  have hc := FamilyTransport.gluing_comm (canonicalDatum f V).transport (fibreDatum f V).transport
    (fun _ => (Over.map f.hom).map (canonicalComponentIso f V).hom)
    (fun _ => Descent.structureMap_naturality _ _)
    (fun {i j Z} v y => by cases i; cases j; exact canonicalComponentIso_move f V v y)
    PUnit.unit PUnit.unit
  rw [Descent.DescentData.transport_gluing, Descent.DescentData.transport_gluing] at hc
  exact hc

end Canonical

variable (B S hS) in
/-- **Étale descent of algebraic spaces along proper surjective morphisms, from descent of
spaces-étale sheaves.** The input of the proof of Stacks 0AGG follows from the proper case of
Stacks 0GFW and the translation step of Stacks 0GG0: effectivity is Stacks 0GG0, read through
`AlgebraicGeometry.Space.canonicalIsoFibreDatum`, and full faithfulness is
`AlgebraicGeometry.Space.etaleSpaceHomDescentAlongProperSurjective_of_descentEffective`. -/
theorem etaleSpaceDescentAlongProperSurjective_of_sheafDescent
    (hproper : DescentEffectiveAlongProperSurjective B S hS)
    (hbridge : EtaleSpaceDescentEffectiveOfSheafDescent B S hS) :
    EtaleSpaceDescentAlongProperSurjective B S hS := fun f hs hp =>
  ⟨fun D hD => by
    obtain ⟨-, V, hV, ⟨e⟩⟩ := isEffective_homDescentData_of_isEtale_of_isProper_isSurjective
      B S hS hproper hbridge f hs hp D hD
    exact ⟨V, hV, ⟨(canonicalIsoFibreDatum f V).symm ≪≫ e⟩⟩,
    etaleSpaceHomDescentAlongProperSurjective_of_descentEffective hproper f hs hp⟩

variable (B S hS) in
/-- **Stacks 0AGG, from descent of spaces-étale sheaves along proper surjections.** Let
`g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally Noetherian; the
coequalizer of the two projections `Y ×_X Y ⟶ Y` exists and has the properties of Stacks 0AGG,
granted the proper case of Stacks 0GFW and the translation step of Stacks 0GG0. -/
theorem properKernelPairCoequalizers_of_sheafDescent
    (hproper : DescentEffectiveAlongProperSurjective B S hS)
    (hbridge : EtaleSpaceDescentEffectiveOfSheafDescent B S hS) :
    ProperKernelPairCoequalizers B S hS :=
  properKernelPairCoequalizers
    (etaleSpaceDescentAlongProperSurjective_of_sheafDescent B S hS hproper hbridge)

variable (B S hS) in
/-- **Stacks 0AGG.** Let `S` be a scheme and let `g : Y ⟶ X` be a morphism of algebraic spaces
over `S` with `X` locally Noetherian and `g` proper. Let `R = Y ×_X Y` with projections
`s, t : R ⟶ Y`. There exists a coequalizer `X'` of `s, t : R ⟶ Y` in the category of algebraic
spaces over `S`. Moreover
1. the morphism `X' ⟶ X` is finite;
2. the morphism `Y ⟶ X'` is proper;
3. the morphism `Y ⟶ X'` is surjective;
4. the morphism `X' ⟶ X` is universally injective;
5. if `g` is surjective, the morphism `X' ⟶ X` is a universal homeomorphism.

The statement `AlgebraicGeometry.Space.ProperKernelPairCoequalizers` consists of exactly these
six clauses: existence of the coequalizer as an
`AlgebraicGeometry.Space.KernelPairCoequalizer` (a colimit cofork of the kernel pair in the
category of algebraic spaces over `S`), and clauses (1) to (5) for every such coequalizer.
Everything is proved here, unconditionally: nothing is carried as a hypothesis. The two inputs
of the proof, the proper case of Stacks 0GFW and the translation step of Stacks 0GG0, are the
theorems `AlgebraicGeometry.Space.descentEffectiveAlongProperSurjective` and
`AlgebraicGeometry.Space.etaleSpaceDescentEffectiveOfSheafDescent`. -/
@[stacks 0AGG]
theorem properKernelPairCoequalizers_holds : ProperKernelPairCoequalizers B S hS :=
  properKernelPairCoequalizers_of_sheafDescent B S hS (descentEffectiveAlongProperSurjective B S hS)
    (etaleSpaceDescentEffectiveOfSheafDescent B S hS)

end AlgebraicGeometry.Space
