module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Composition
import all StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.Composition
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.DiagonalUniqueness
public import StacksFrontier.AlgebraicGeometry.Duality.CompactlySupportedCohomology.ShriekTrianglesData

/-!
# Composition of compactly supported direct images

Let `Rg_! : 𝒞 ⥤ Pro-𝒟` be a functor whose values are pro-objects with countable index, and let
`M = (M_n)` be an inverse sequence in `𝒞`, as produced by a first compactly supported direct
image `Rf_!`. Applying `Rg_!` termwise gives an inverse system in `Pro-𝒟`, and there is an inverse
sequence `N = (N_k)` in `𝒟`, unique up to pro-isomorphism, with
`Hom(N, L) = colim_n Hom(Rg_! M_n, L)` naturally in `L`. This is the composition `Rg_! ∘ Rf_!` of
[Stacks, Tag 0G54], built from [Stacks, Tag 0G53].

The colimit `colim_n Hom(Rg_! M_n, -)` depends on `M` only through its pro-object: a
pro-isomorphism `M ≅ M'` induces an isomorphism of the two colimits
(`CategoryTheory.ProSeq.colimitIsoOfProIso`). So the construction is attached to a pro-object
`P` of `𝒞`, not to a chosen inverse system: `CategoryTheory.ProSeq.bindObj G P`. For the functors
`Rf_!` and `Rg_!` of composable morphisms of `FTS_S` this is `AlgebraicGeometry.lowerShriekComp`.

## Main definitions

* `CategoryTheory.Pro.CompositionRepresentation` packages such an inverse sequence `N` together
  with the natural identification of its functor of points.
* `CategoryTheory.ProSeq.bindObj`: the pro-object `colim_n Hom(G M_n, -)` attached to a functor
  `G : 𝒞 ⥤ Pro-𝒟` and a pro-object `P = (M_n)` of `𝒞`.
* `AlgebraicGeometry.lowerShriekComp`: **Stacks 0G54**, the composition `Rg_! Rf_! K`.

## Main results

* `CategoryTheory.Pro.exists_compositionRepresentation` constructs the composition.
* `CategoryTheory.Pro.CompositionRepresentation.homColimitIso` is the displayed colimit formula.
* `CategoryTheory.Pro.compositionRepresentation_uniqueUpToIso` gives uniqueness up to
  pro-isomorphism.
* `CategoryTheory.ProSeq.colimitIsoOfProIso`: a pro-isomorphism of inverse sequences induces an
  isomorphism of the colimits of any functor along them.
* `AlgebraicGeometry.lowerShriekCompPointsIso` and
  `AlgebraicGeometry.nonempty_iso_lowerShriekComp_iff`: **Stacks 0G54**, the defining property of
  `Rg_! Rf_! K` for every inverse system giving `Rf_! K`, and its uniqueness up to
  pro-isomorphism.

## Implementation notes

A pro-object is used through its functor of points `N ↦ colim_k Hom(N_k, N)`, which is
`CategoryTheory.Pro.coyonedaColim`; this embedding is contravariant, so a functor with values in
pro-objects of `𝒟` appears as a functor `𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v`, and the inverse system `(M_n)`
becomes the direct system `M.rightOp ⋙ G` of such functors. The comparison is an isomorphism of
functors, hence natural in the test object `L`. Functoriality in `K` is not asserted: the source
omits it, saying it follows from Tag 0G55.

## References

* [Stacks Project, Tag 0G54](https://stacks.math.columbia.edu/tag/0G54)
* [Stacks Project, Tag 0G53](https://stacks.math.columbia.edu/tag/0G53)
* [Stacks Project, Tag 0G4Z](https://stacks.math.columbia.edu/tag/0G4Z)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v v' u u'

namespace CategoryTheory.Pro

end CategoryTheory.Pro

namespace CategoryTheory.ProSeq

variable {𝒞 : Type u'} [Category.{v} 𝒞] {𝒟 : Type u} [Category.{v} 𝒟]

section ColimitOfProIso

variable {E : Type*} [Category E] [HasColimitsOfShape ℕ E] (H : 𝒞ᵒᵖ ⥤ E)

/-- The morphism `colim_n H(M_n) ⟶ colim_n H(M'_n)` induced by the backward maps
`M'_{β n} ⟶ M_n` of a pro-isomorphism `M ≅ M'`. -/
public noncomputable def colimitMapOfProIso {M M' : ℕᵒᵖ ⥤ 𝒞}
    (e : InverseSequence.ProIso M M') : colimit (M.rightOp ⋙ H) ⟶ colimit (M'.rightOp ⋙ H) :=
  colimit.desc (M.rightOp ⋙ H)
    { pt := colimit (M'.rightOp ⋙ H)
      ι :=
        { app := fun n => H.map (e.ψ n).op ≫ colimit.ι (M'.rightOp ⋙ H) (e.β n)
          naturality := by
            intro n m f
            have h : n ≤ m := leOfHom f
            obtain rfl : f = homOfLE h := Subsingleton.elim _ _
            change H.map (InverseSequence.tr M h).op ≫ H.map (e.ψ m).op ≫ _ =
              (H.map (e.ψ n).op ≫ _) ≫ 𝟙 _
            rw [Category.comp_id, ← Category.assoc, ← H.map_comp, ← op_comp, ← e.ψnat h,
              op_comp, H.map_comp, Category.assoc]
            exact congrArg (H.map (e.ψ n).op ≫ ·)
              (colimit.w (M'.rightOp ⋙ H) (homOfLE (e.βmono h))) } }

/-- The leg of `CategoryTheory.ProSeq.colimitMapOfProIso` at a stage `n`. -/
@[reassoc]
public lemma ι_colimitMapOfProIso {M M' : ℕᵒᵖ ⥤ 𝒞} (e : InverseSequence.ProIso M M') (n : ℕ) :
    colimit.ι (M.rightOp ⋙ H) n ≫ colimitMapOfProIso H e =
      H.map (e.ψ n).op ≫ colimit.ι (M'.rightOp ⋙ H) (e.β n) :=
  colimit.ι_desc (F := M.rightOp ⋙ H) _ n

/-- The morphisms of colimits induced by the two directions of a pro-isomorphism are mutually
inverse: forward after backward is a transition morphism, which the colimit does not see. -/
public lemma colimitMapOfProIso_comp_symm {M M' : ℕᵒᵖ ⥤ 𝒞} (e : InverseSequence.ProIso M M') :
    colimitMapOfProIso H e ≫ colimitMapOfProIso H e.symm = 𝟙 _ := by
  refine colimit.hom_ext fun n => ?_
  rw [ι_colimitMapOfProIso_assoc, ι_colimitMapOfProIso, Category.comp_id, ← H.map_comp_assoc,
    ← op_comp]
  change H.map (e.φ (e.β n) ≫ e.ψ n).op ≫ colimit.ι (M.rightOp ⋙ H) (e.α (e.β n)) = _
  rw [e.ψφ n]
  exact colimit.w (M.rightOp ⋙ H) (homOfLE _)

/-- **A pro-isomorphism of inverse sequences induces an isomorphism of colimits.** For any functor
`H : 𝒞ᵒᵖ ⥤ E`, a pro-isomorphism `M ≅ M'` gives `colim_n H(M_n) ≅ colim_n H(M'_n)`. -/
public noncomputable def colimitIsoOfProIso {M M' : ℕᵒᵖ ⥤ 𝒞} (e : InverseSequence.ProIso M M') :
    colimit (M.rightOp ⋙ H) ≅ colimit (M'.rightOp ⋙ H) where
  hom := colimitMapOfProIso H e
  inv := colimitMapOfProIso H e.symm
  hom_inv_id := colimitMapOfProIso_comp_symm H e
  inv_hom_id := colimitMapOfProIso_comp_symm H e.symm

end ColimitOfProIso

/-- The functors of points of the values of a functor `G : 𝒞 ⥤ Pro-𝒟`, as a functor
`𝒞ᵒᵖ ⥤ (𝒟 ⥤ Type v)`: it sends `K` to `L ↦ Hom_{Pro-𝒟}(G K, L)`. -/
public abbrev pointsFunctor (G : 𝒞 ⥤ ProSeq 𝒟) : 𝒞ᵒᵖ ⥤ 𝒟 ⥤ Type v :=
  G.leftOp ⋙ (IsSequentialProObject 𝒟).ι

/-- An inverse sequence whose pro-object is `P`. -/
public noncomputable def seqOf (P : ProSeq 𝒞) : ℕᵒᵖ ⥤ 𝒞 :=
  P.unop.property.choose

/-- The pro-object of `CategoryTheory.ProSeq.seqOf P` is `P`. -/
public noncomputable def ofSeqOfIso (P : ProSeq 𝒞) : of (seqOf P) ≅ P :=
  (ObjectProperty.isoMk _ P.unop.property.choose_spec.some).op

/-- Every pro-object is the pro-object of an inverse sequence. -/
public lemma exists_iso_of (P : ProSeq 𝒞) : ∃ M : ℕᵒᵖ ⥤ 𝒞, Nonempty (of M ≅ P) :=
  ⟨seqOf P, ⟨ofSeqOfIso P⟩⟩

/-- **[Stacks, Tag 0G53] for a termwise image.** For `G : 𝒞 ⥤ Pro-𝒟` and an inverse sequence `M`
in `𝒞`, the functor `L ↦ colim_n Hom(G M_n, L)` is the functor of points of a pro-object of `𝒟`
with countable index, namely of the diagonal inverse sequence of
`CategoryTheory.Pro.exists_diagonalRepresentation`. -/
public lemma isSequentialProObject_colimit (G : 𝒞 ⥤ ProSeq 𝒟) (M : ℕᵒᵖ ⥤ 𝒞) :
    IsSequentialProObject 𝒟 (colimit (M.rightOp ⋙ pointsFunctor G)) := by
  obtain ⟨r⟩ := Pro.exists_diagonalRepresentation (M.rightOp ⋙ pointsFunctor G)
    (fun n => seqOf (G.obj (M.obj (op n))))
    (fun n => (G.obj (M.obj (op n))).unop.property.choose_spec.some)
  exact ⟨r.system, ⟨r.comparison⟩⟩

/-- **The extension of `G : 𝒞 ⥤ Pro-𝒟` to a pro-object** `P = (M_n)` of `𝒞`: the pro-object of `𝒟`
whose functor of points is `L ↦ colim_n Hom(G M_n, L)`. It exists by [Stacks, Tag 0G53]
(`CategoryTheory.ProSeq.isSequentialProObject_colimit`), and it does not depend on the inverse
sequence chosen for `P` (`CategoryTheory.ProSeq.bindObjPointsIso`). -/
public noncomputable def bindObj (G : 𝒞 ⥤ ProSeq 𝒟) (P : ProSeq 𝒞) : ProSeq 𝒟 :=
  op ⟨colimit ((seqOf P).rightOp ⋙ pointsFunctor G),
    isSequentialProObject_colimit G (seqOf P)⟩

/-- For every inverse sequence `M` giving `P`, the functor of points of
`CategoryTheory.ProSeq.bindObj G P` is `L ↦ colim_n Hom(G M_n, L)`: the inverse sequences giving
`P` are pro-isomorphic, and the colimit only sees `M` up to pro-isomorphism. -/
public noncomputable def bindObjPointsIso (G : 𝒞 ⥤ ProSeq 𝒟) {P : ProSeq 𝒞} {M : ℕᵒᵖ ⥤ 𝒞}
    (e : of M ≅ P) : (bindObj G P).points ≅ colimit (M.rightOp ⋙ pointsFunctor G) :=
  colimitIsoOfProIso (pointsFunctor G) (proIsoOfIso (ofSeqOfIso P ≪≫ e.symm))

/-- **Uniqueness up to pro-isomorphism.** For an inverse sequence `M` giving `P`, an inverse
sequence `N` of `𝒟` satisfies `Hom(N, L) = colim_n Hom(G M_n, L)` naturally in `L` if and only if
its pro-object is `CategoryTheory.ProSeq.bindObj G P`. -/
public theorem nonempty_iso_bindObj_iff (G : 𝒞 ⥤ ProSeq 𝒟) {P : ProSeq 𝒞} {M : ℕᵒᵖ ⥤ 𝒞}
    (e : of M ≅ P) (N : ℕᵒᵖ ⥤ 𝒟) :
    Nonempty ((of N).points ≅ colimit (M.rightOp ⋙ pointsFunctor G)) ↔
      Nonempty (of N ≅ bindObj G P) :=
  ⟨fun ⟨i⟩ => ⟨(ObjectProperty.isoMk _ (bindObjPointsIso G e ≪≫ i.symm)).op⟩,
    fun ⟨i⟩ => ⟨((IsSequentialProObject 𝒟).ι.mapIso i.unop).symm ≪≫ bindObjPointsIso G e⟩⟩

end CategoryTheory.ProSeq

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe w

variable {S : Scheme.{w}} [IsNoetherian S] {X Y Z : FTS S}

/-- **`Rf_! K` is given by an inverse system**, by the very construction of `Rf_!`: the termwise
derived direct image `(Rf̄_* K̄_n)` of the Deligne system `(K̄_n)` with value `K` that defines
`Rj_! K` ([Stacks, Tag 0G4N]). -/
public noncomputable def lowerShriekObjIso (f : X ⟶ Y) (c : CompactificationOf (Over.mk f.left))
    (K : BoundedCoherentDerived X.left) :
    ProSeq.of ((CompactificationData.ofOpenImmersion c.immersion c.toBase).assignment.system K ⋙
        properPushforwardBoundedCoherent c.toBase) ≅ (lowerShriek f c).obj K :=
  (ProSeq.mapOfIso _ _).symm ≪≫ (ProSeq.map _).mapIso (extensionByZeroIso _ _ K).symm

/-- **Stacks Project, Tag 0G54**, the definition. In Situation [Stacks, Tag 0F42] let
`f : X ⟶ Y` and `g : Y ⟶ Z` be composable morphisms of `FTS_S`, with compactifications `cf` of `X`
over `Y` and `cg` of `Y` over `Z` defining `Rf_!` and `Rg_!` ([Stacks, Section 0G4Z],
`AlgebraicGeometry.lowerShriek`). For `K` in `D^b_{Coh}(𝒪_X)`, `Rf_! K` is given by an inverse
system `(M_n)` of `D^b_{Coh}(𝒪_Y)` (`AlgebraicGeometry.lowerShriekObjIso`), `(Rg_! M_n)` is an
inverse system of `Pro-D^b_{Coh}(𝒪_Z)`, and `Rg_! Rf_! K` is the pro-object of `D^b_{Coh}(𝒪_Z)`
given by [Stacks, Tag 0G53] with

`Hom(Rg_! Rf_! K, L) = colim_n Hom(Rg_! M_n, L)`

for every `L` (`AlgebraicGeometry.lowerShriekCompPointsIso`); it is unique up to pro-isomorphism
(`AlgebraicGeometry.nonempty_iso_lowerShriekComp_iff`) and does not depend on the inverse system
`(M_n)` chosen. Functoriality in `K` is omitted, as in the source. -/
@[stacks 0G54 "the definition of Rg_! Rf_! K"]
public noncomputable def lowerShriekComp (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) : ProSeq (BoundedCoherentDerived Z.left) :=
  ProSeq.bindObj (lowerShriek g cg) ((lowerShriek f cf).obj K)

/-- **Stacks Project, Tag 0G54**, the defining property: for every inverse system `(M_n)` of
`D^b_{Coh}(𝒪_Y)` giving `Rf_! K`,

`Hom(Rg_! Rf_! K, L) = colim_n Hom(Rg_! M_n, L)`

naturally in `L` in `D^b_{Coh}(𝒪_Z)`. -/
@[stacks 0G54 "Hom(Rg_! Rf_! K, L) = colim_n Hom(Rg_! M_n, L) for every inverse system (M_n) \
giving Rf_! K"]
public noncomputable def lowerShriekCompPointsIso (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) {M : ℕᵒᵖ ⥤ BoundedCoherentDerived Y.left}
    (e : ProSeq.of M ≅ (lowerShriek f cf).obj K) :
    (lowerShriekComp f g cf cg K).points ≅
      colimit (M.rightOp ⋙ ProSeq.pointsFunctor (lowerShriek g cg)) :=
  ProSeq.bindObjPointsIso _ e

/-- **Stacks Project, Tag 0G54**, the displayed formula with `Hom`-sets of pro-objects: for every
inverse system `(M_n)` giving `Rf_! K` and every `L` in `D^b_{Coh}(𝒪_Z)`,

`Hom_{Pro}(Rg_! Rf_! K, L) = colim_n Hom_{Pro}(Rg_! M_n, L)`. -/
@[stacks 0G54 "Hom_Pro(Rg_! Rf_! K, L) = colim_n Hom_Pro(Rg_! M_n, L)"]
public noncomputable def lowerShriekCompHomEquiv (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) {M : ℕᵒᵖ ⥤ BoundedCoherentDerived Y.left}
    (e : ProSeq.of M ≅ (lowerShriek f cf).obj K) (L : BoundedCoherentDerived Z.left) :
    (lowerShriekComp f g cf cg K ⟶ ProSeq.const.obj L) ≃
      colimit (M.rightOp ⋙ (lowerShriek g cg).op ⋙ yoneda.obj (ProSeq.const.obj L)) :=
  (ProSeq.homConstEquiv _ L).trans <|
    ((lowerShriekCompPointsIso f g cf cg K e).app L ≪≫
      colimitObjIsoColimitCompEvaluation _ L ≪≫
      HasColimit.isoOfNatIso
        (G := M.rightOp ⋙ (lowerShriek g cg).op ⋙ yoneda.obj (ProSeq.const.obj L))
        (NatIso.ofComponents
          (fun n => (ProSeq.homConstEquiv ((lowerShriek g cg).obj (M.obj (op n))) L).symm.toIso)
          (fun {n _} φ => by
            ext x
            apply Quiver.Hom.unop_inj
            apply ObjectProperty.hom_ext
            ext T h
            exact (NatTrans.naturality_apply ((lowerShriek g cg).map (M.map φ.op)).unop.hom h
              (show ((lowerShriek g cg).obj (M.obj (op n))).points.obj L from x)).symm))).toEquiv

/-- **Stacks Project, Tag 0G54**, uniqueness: for an inverse system `(M_n)` giving `Rf_! K`, an
inverse system `(N_k)` of `D^b_{Coh}(𝒪_Z)` satisfies `Hom((N_k), L) = colim_n Hom(Rg_! M_n, L)`
naturally in `L` if and only if it gives `Rg_! Rf_! K`; so `Rg_! Rf_! K` is the unique
pro-isomorphism class with that property. -/
@[stacks 0G54 "uniqueness up to pro-isomorphism"]
public theorem nonempty_iso_lowerShriekComp_iff (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (K : BoundedCoherentDerived X.left) {M : ℕᵒᵖ ⥤ BoundedCoherentDerived Y.left}
    (e : ProSeq.of M ≅ (lowerShriek f cf).obj K) (N : ℕᵒᵖ ⥤ BoundedCoherentDerived Z.left) :
    Nonempty ((ProSeq.of N).points ≅
        colimit (M.rightOp ⋙ ProSeq.pointsFunctor (lowerShriek g cg))) ↔
      Nonempty (ProSeq.of N ≅ lowerShriekComp f g cf cg K) :=
  ProSeq.nonempty_iso_bindObj_iff _ e N

end AlgebraicGeometry
