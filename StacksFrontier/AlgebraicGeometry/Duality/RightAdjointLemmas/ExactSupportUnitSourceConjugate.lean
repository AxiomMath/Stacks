module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportPushforwardInternalHom
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.UnitSourceConjugate

/-!
# Evaluation at the unit section, as a conjugate of a tensor transformation

Let `(C, J, O)` be a ringed site, let `M` be a sheaf of `O`-modules and let `u : O ⟶ M` be a
morphism — in the application, the unit `𝒪_X ⟶ i_* 𝒪_Z` of a closed quotient morphism. Then
there is a map

`ℰom_O(M, -) ⟶ ℰom_O(O, -) ≅ 𝟭`,

restriction along `u` followed by the trivialisation of [Stacks, Tag 03EM]: **evaluation at the
unit section**, read on `ℰom_O(M, -)`. This file identifies it as a conjugate.

Both `ℰom_O(M, -)` and `𝟭` are right adjoints, of `M ⊗_O -` and of the identity functor, so a
transformation between them is the conjugate (`CategoryTheory.conjugateEquiv`) of a
transformation `𝟭 ⟶ M ⊗_O -` of the left adjoints. The one it is the conjugate of is the
evident one: the inverse left unitor `𝟭 ≅ O ⊗_O -` followed by `u ⊗_O -`.

This is the right-hand side of the underived core of the remaining obligation of
[Stacks, Tag 0B4B] (see `StacksFrontier/AlgebraicGeometry/Duality/`
`EffectiveCartierDualTriangleComparison.lean`, "What is not done"). Its left-hand side, the
underived form of [Stacks, Tag 0E2I] at the source `𝒪_Z`, is also a conjugate — of the
projection formula, by
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_hom`
— over the *same* adjunction
`…ClosedQuotientMorphismOfRingedSpaces.tensorPushforwardAdjunction`, which is
`Stacks.SheafOfModules.InternalHom.sheafTensorHomAdjunction` at `i_* 𝒪_Z`. So with this
identification both sides of that core are conjugates for one and the same first adjunction,
and comparing them is comparing transformations of tensor functors.

The file also carries the *other* side's trace to the same adjunction. The counit of
[Stacks, Tag 0A75] is the conjugate of the unit `𝟭 ⟶ i_* i^*` for the **twofold** composite
`(i^* ⊣ i_*).comp (i_* ⊣ ℰom(𝒪_Z, -))` (`CategoryTheory.counit_eq_conjugateEquiv_unit`), whereas
the underived form of [Stacks, Tag 0E2I] is stated over the **threefold** composite
`…ClosedQuotientMorphismOfRingedSpaces.pushforwardTensorPullbackAdjunction`, whose middle factor
is the tensor--internal-Hom adjunction on `Z` at `𝒪_Z`. Composing the trace after the
trivialisation of that middle factor crosses from the one to the other:
`CategoryTheory.whiskerRight_conjugateEquiv_comp_counit`.

## Main results

* `Stacks.SheafOfModules.InternalHom.internalHomPrecompNatTrans_comp_unitIso`: **evaluation at
  the unit section along `u : O ⟶ M` is the conjugate of the inverse left unitor followed by
  `u ⊗_O -`.**
* `CategoryTheory.whiskerRight_conjugateEquiv_comp_counit`: **the trace of a composite
  adjunction, precomposed with the trivialisation of a middle tensor factor, is the conjugate for
  the threefold composite** of the unit of the outer adjunction followed by the whiskered
  trivialising transformation. Its two auxiliaries are
  `CategoryTheory.Adjunction.id_comp_homEquiv_apply` and
  `CategoryTheory.conjugateEquiv_comp_id_comp`.
* `Stacks.SheafOfModules.InternalHom.whiskerRight_internalHomSecondFunctorUnitIso_comp_counit`:
  **the trivialisation of `ℰom_O(O, -)`, whiskered into a composite adjunction and followed by
  the trace, is the conjugate of the inverse left unitor** for the threefold composite. This is
  the form in which the trace of [Stacks, Tag 0A75] meets the underived form of
  [Stacks, Tag 0E2I], and it is stated with the site and sheaf of rings still variable so that
  the inverse left unitor can be written at all.
* `Stacks.SheafOfModules.InternalHom`
  `.whiskerRight_internalHomSecondFunctorUnitIso_comp_counit_symm`: the same with the inverse left
  unitor named as the conjugate preimage of the trivialisation, which is the form that can be
  stated at a ringed space.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
  `.internalHomSecondFunctorUnitIso_whiskered_comp_counit`: **that identity at a closed quotient
  morphism of ringed spaces, over `…pushforwardTensorPullbackAdjunction` at `𝒪_Z`** — step (a)
  of the underived core of the remaining obligation of [Stacks, Tag 0B4B].
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces`
  `.whiskerRight_conjugateEquiv_comp_counit_exactSupport`: **that identity at a closed quotient
  morphism of ringed spaces**, over the threefold composite that
  `…pushforwardTensorPullbackAdjunction` at `𝒪_Z` is
  (`…pushforwardTensorPullbackAdjunction_eq`), which is the adjunction the underived form of
  [Stacks, Tag 0E2I] is stated over.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

noncomputable section

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section Threefold

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **The hom-equivalence of `Adjunction.id.comp adj` is that of `adj`.**  Composing an
adjunction with the identity adjunction on its left changes the hom-equivalence by the identity
in front, which `CategoryTheory.Adjunction.comp_homEquiv_apply` exhibits. -/
theorem Adjunction.id_comp_homEquiv_apply {L : D ⥤ C} {R : C ⥤ D} (adj : L ⊣ R) (d : D) (X : C)
    (f : L.obj d ⟶ X) :
    (Adjunction.id.comp adj).homEquiv d X f = adj.homEquiv d X f := by
  simp [Adjunction.homEquiv_unit]

/-- **The counit of `R₁ ⊣ R₂` as a conjugate for a composite that carries the identity
adjunction in the middle.**  This is `CategoryTheory.counit_eq_conjugateEquiv_unit` for the
adjunction `adjP.comp (Adjunction.id.comp adjE)` rather than `adjP.comp adjE`: the two have the
same hom-equivalence by `CategoryTheory.Adjunction.id_comp_homEquiv_apply`, and a conjugate is
pinned down by its compatibility with the hom-equivalences
(`CategoryTheory.conjugateEquiv_eq_of_homEquiv`).

The point of the detour is that the identity adjunction in the middle is what a *threefold*
composite degenerates to when its middle factor is trivialised, and that is how the trace of
[Stacks, Tag 0A75] reaches the threefold adjunction
`…ClosedQuotientMorphismOfRingedSpaces.pushforwardTensorPullbackAdjunction`. -/
theorem conjugateEquiv_comp_id_comp {P : C ⥤ D} {Q : D ⥤ C} {E : C ⥤ D} (adjP : P ⊣ Q)
    (adjE : Q ⊣ E) :
    conjugateEquiv (adjP.comp (Adjunction.id.comp adjE)) Adjunction.id adjP.unit =
      adjE.counit := by
  refine conjugateEquiv_eq_of_homEquiv _ _ _ _ (fun c X f ↦ ?_)
  have h : (adjP.comp (Adjunction.id.comp adjE)).homEquiv c X f =
      (adjP.comp adjE).homEquiv c X f := by
    refine Eq.trans (Adjunction.comp_homEquiv_apply adjP (Adjunction.id.comp adjE) c X f) ?_
    refine Eq.trans ?_ (Adjunction.comp_homEquiv_apply adjP adjE c X f).symm
    exact congrArg (fun g ↦ adjP.homEquiv c (E.obj X) g)
      (Adjunction.id_comp_homEquiv_apply adjE (P.obj c) X f)
  rw [h, counit_eq_conjugateEquiv_unit adjP adjE]
  exact homEquiv_comp_conjugateEquiv (adjP.comp adjE) Adjunction.id adjP.unit c X f

/-- **The trace of a composite adjunction with a trivialised middle factor, as a conjugate for
the threefold composite.**  Let `adjP : P ⊣ Q`, `adjE : Q ⊣ E` and `adjT : T ⊣ H` be adjunctions
with `P : C ⥤ D`, `Q : D ⥤ C`, `E : C ⥤ D` and `T H : D ⥤ D`, and let `ζ : 𝟭 D ⟶ T`.  Then the
conjugate of `ζ` — a transformation `H ⟶ 𝟭 D` — whiskered into `E` and then by `Q`, followed by
the counit of `adjE`, is the conjugate for the *threefold* adjunction
`adjP.comp (adjT.comp adjE)` of the unit of `adjP` followed by `ζ` whiskered the same way.

In the application `P` is the pullback `i^*` of a closed quotient morphism, `Q` the direct image
`i_*`, `E` the sheaf Hom with exact support of [Stacks, Tag 0A75], `adjT` the
tensor--internal-Hom adjunction of [Stacks, Tag 03EO] at the structure sheaf `𝒪_Z` and `ζ` the
inverse left unitor: the statement is that the trace `i_* ℰom(𝒪_Z, -) ⟶ 𝟭` of
[Stacks, Tag 0A75], composed after the trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)`, is a conjugate for
`…ClosedQuotientMorphismOfRingedSpaces.pushforwardTensorPullbackAdjunction`, which is the
adjunction the underived form of [Stacks, Tag 0E2I] is stated over.

The proof strips the two outer factors of the composite adjunction with
`CategoryTheory.conjugateEquiv_comp_right` and `conjugateEquiv_comp_left`, leaving
`Adjunction.id` where `adjT` was, and then puts the counit in by
`CategoryTheory.conjugateEquiv_comp_id_comp`; the two conjugates compose by
`CategoryTheory.conjugateEquiv_comp`. -/
theorem whiskerRight_conjugateEquiv_comp_counit {P : C ⥤ D} {Q : D ⥤ C} {E : C ⥤ D}
    {T H : D ⥤ D} (adjP : P ⊣ Q) (adjE : Q ⊣ E) (adjT : T ⊣ H) (ζ : 𝟭 D ⟶ T) :
    Functor.whiskerRight (Functor.whiskerLeft E (conjugateEquiv adjT Adjunction.id ζ)) Q ≫
        adjE.counit =
      conjugateEquiv (adjP.comp (adjT.comp adjE)) Adjunction.id
        (adjP.unit ≫ Functor.whiskerLeft P (Functor.whiskerRight ζ Q)) := by
  have h1 : conjugateEquiv (adjT.comp adjE) (Adjunction.id.comp adjE)
        (Functor.whiskerRight ζ Q) =
      Functor.whiskerLeft E (conjugateEquiv adjT Adjunction.id ζ) :=
    conjugateEquiv_comp_right adjT Adjunction.id adjE ζ
  have h2 : conjugateEquiv (adjP.comp (adjT.comp adjE))
        (adjP.comp (Adjunction.id.comp adjE))
        (Functor.whiskerLeft P (Functor.whiskerRight ζ Q)) =
      Functor.whiskerRight (Functor.whiskerLeft E (conjugateEquiv adjT Adjunction.id ζ)) Q :=
    Eq.trans
      (conjugateEquiv_comp_left adjP (adjT.comp adjE) (Adjunction.id.comp adjE)
        (Functor.whiskerRight ζ Q))
      (congrArg (fun γ ↦ Functor.whiskerRight γ Q) h1)
  refine Eq.trans ?_
    (conjugateEquiv_comp (adjP.comp (adjT.comp adjE)) (adjP.comp (Adjunction.id.comp adjE))
      Adjunction.id (Functor.whiskerLeft P (Functor.whiskerRight ζ Q)) adjP.unit)
  rw [h2, conjugateEquiv_comp_id_comp adjP adjE]

end Threefold

end CategoryTheory

namespace Stacks.SheafOfModules.InternalHom

universe u

variable {D : Type u} [Category.{u} D] (K : GrothendieckTopology D)
  (O : Sheaf K CommRingCat.{u})
  [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.monoidalClosed

/-- **Evaluation at the unit section, read on `ℰom_O(M, -)`, is a conjugate.** For
`u : O ⟶ M`, restriction along `u` followed by the trivialisation
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso` of `ℰom_O(O, -)` is the
conjugate — for the adjunction of [Stacks, Tag 03EO] at `M` and the identity adjunction — of the
transformation `𝟭 ⟶ M ⊗_O -` given by the inverse left unitor followed by `u ⊗_O -`.

Restriction along `u` is itself the conjugate of `u ⊗_O -`
(`Stacks.SheafOfModules.InternalHom.conjugateEquiv_sheafTensor_map_precomp`) and the
trivialisation is the conjugate of the inverse left unitor
(`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_eq_sheafTensor`), so
this is `CategoryTheory.conjugateEquiv_comp`. -/
theorem internalHomPrecompNatTrans_comp_unitIso
    {M : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)}
    (u : _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O) ⟶ M) :
    internalHomPrecompNatTrans K O u ≫ (internalHomSecondFunctorUnitIso O).hom =
      conjugateEquiv (sheafTensorHomAdjunction O M) Adjunction.id
        ((((leftUnitorNatIso _).inv ≫
              (tensoringLeft _).map (_root_.SheafOfModules.unitIso O).hom) ≫
            (_root_.SheafOfModules.sheafTensorIsoApp O
              (_root_.SheafOfModules.unit
                ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))).hom) ≫
          (Stacks.SheafOfModules.Tensor.sheafTensor O).map u) := by
  rw [← conjugateEquiv_sheafTensor_map_precomp K O u,
    internalHomSecondFunctorUnitIso_hom_eq_sheafTensor O, conjugateEquiv_comp]

/-- **The trivialisation of `ℰom_O(O, -)`, whiskered into a composite adjunction and followed by
the trace, is a conjugate of the inverse left unitor.**  Let `adjP : P ⊣ Q` and `adjE : Q ⊣ E` be
adjunctions with `Q` out of `Mod(O)`, so that `E ⋙ Q` is the right adjoint of `P ⋙ Q`; whisker
the trivialisation `ℰom_O(O, -) ≅ 𝟭` of [Stacks, Tag 03EM] into `E` and then by `Q`, and compose
with the counit of `adjE`.  The result is the conjugate — for the *threefold* composite of
`adjP`, the adjunction of [Stacks, Tag 03EO] at `O` and `adjE`, against the identity adjunction —
of the unit of `adjP` followed by the inverse left unitor whiskered the same way.

In the application `P` is the pullback `i^*` of a closed quotient morphism of ringed spaces, `Q`
the direct image `i_*` and `E` the sheaf Hom with exact support of [Stacks, Tag 0A75]: the
statement is that the trace `i_* ℰom(𝒪_Z, -) ⟶ 𝟭` of [Stacks, Tag 0A75], composed after the
trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)`, is a conjugate for the threefold adjunction
`…ClosedQuotientMorphismOfRingedSpaces.pushforwardTensorPullbackAdjunction` at `𝒪_Z`, which is
the adjunction the underived form of [Stacks, Tag 0E2I] is stated over. -/
theorem whiskerRight_internalHomSecondFunctorUnitIso_comp_counit {A : Type (u + 1)}
    [Category.{u} A]
    {P : A ⥤ _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)}
    {Q : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O) ⥤ A}
    {E : A ⥤ _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)}
    (adjP : P ⊣ Q) (adjE : Q ⊣ E) :
    Functor.whiskerRight (Functor.whiskerLeft E (internalHomSecondFunctorUnitIso O).hom) Q ≫
        adjE.counit =
      conjugateEquiv
        (adjP.comp
          ((sheafTensorHomAdjunction O
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))).comp adjE))
        Adjunction.id
        (adjP.unit ≫
          Functor.whiskerLeft P
            (Functor.whiskerRight
              (((leftUnitorNatIso _).inv ≫
                    (tensoringLeft _).map (_root_.SheafOfModules.unitIso O).hom) ≫
                  (_root_.SheafOfModules.sheafTensorIsoApp O
                    (_root_.SheafOfModules.unit
                      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))).hom)
              Q)) :=
  Eq.trans
    (congrArg (fun τ ↦ Functor.whiskerRight (Functor.whiskerLeft E τ) Q ≫ adjE.counit)
      (internalHomSecondFunctorUnitIso_hom_eq_sheafTensor O))
    (whiskerRight_conjugateEquiv_comp_counit adjP adjE
      (sheafTensorHomAdjunction O
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))) _)

/-- **The same identity with the inverse left unitor replaced by the conjugate preimage of the
trivialisation.**  This is the form that can be *stated* at a ringed space: the inverse left
unitor cannot be written there (see
`whiskerRight_internalHomSecondFunctorUnitIso_comp_counit`), but
`(conjugateEquiv (sheafTensorHomAdjunction O O) Adjunction.id).symm` of the trivialisation can,
and by `internalHomSecondFunctorUnitIso_hom_eq_sheafTensor` it *is* the inverse left unitor. -/
theorem whiskerRight_internalHomSecondFunctorUnitIso_comp_counit_symm {A : Type (u + 1)}
    [Category.{u} A]
    {P : A ⥤ _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)}
    {Q : _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O) ⥤ A}
    {E : A ⥤ _root_.SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)}
    (adjP : P ⊣ Q) (adjE : Q ⊣ E) :
    Functor.whiskerRight (Functor.whiskerLeft E (internalHomSecondFunctorUnitIso O).hom) Q ≫
        adjE.counit =
      conjugateEquiv
        (adjP.comp
          ((sheafTensorHomAdjunction O
            (_root_.SheafOfModules.unit
              ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))).comp adjE))
        Adjunction.id
        (adjP.unit ≫
          Functor.whiskerLeft P
            (Functor.whiskerRight
              ((conjugateEquiv
                  (sheafTensorHomAdjunction O
                    (_root_.SheafOfModules.unit
                      ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
                  Adjunction.id).symm (internalHomSecondFunctorUnitIso O).hom)
              Q)) :=
  Eq.trans
    (congrArg (fun τ ↦ Functor.whiskerRight (Functor.whiskerLeft E τ) Q ≫ adjE.counit)
      (Equiv.apply_symm_apply
        (conjugateEquiv
          (sheafTensorHomAdjunction O
            (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O)))
          Adjunction.id) _).symm)
    (whiskerRight_conjugateEquiv_comp_counit adjP adjE
      (sheafTensorHomAdjunction O
        (_root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := K)) O))) _)

end Stacks.SheafOfModules.InternalHom

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

open Stacks.SheafOfModules.InternalHom

universe u

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The structure sheaf of `Z` as a module over itself, in the spelling of the ringed site
`siteZ` — the spelling the trivialisation
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso` is stated in. -/
abbrev structureSheafModuleZ : SheafOfModules.{u} (structureSheafRing S.Z) :=
  _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf (J := S.siteZ)) S.Z.sheaf)

/-- **The threefold adjunction of the underived form of [Stacks, Tag 0E2I], unfolded.**  Two
delta steps: `pushforwardTensorPullbackAdjunction` is the pullback--pushforward adjunction of
[Stacks, Tag 0096] composed with `tensorPushforwardExactSupportAdjunction`, which is in turn the
tensor--internal-Hom adjunction of [Stacks, Tag 03EO] on `Z` composed with the exact-support
adjunction of [Stacks, Tag 0A75].  Spelling the composite out is what lets a generic statement
about `adj₁.comp (adj₂.comp adj₃)` be applied without the unifier being asked to discover the
unfolding underneath a `CategoryTheory.conjugateEquiv`. -/
theorem pushforwardTensorPullbackAdjunction_eq (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    S.pushforwardTensorPullbackAdjunction N =
      (modulePullbackPushforwardAdjunction S.i).comp
        ((sheafTensorHomAdjunction S.Z.sheaf N).comp
          S.modulePushforwardSheafHomExactSupportAdjunction) :=
  rfl

/-- **The trace of [Stacks, Tag 0A75], after the trivialisation of a middle tensor factor at
`𝒪_Z`, is a conjugate for the threefold adjunction of the underived form of
[Stacks, Tag 0E2I].**  This is the generic
`CategoryTheory.whiskerRight_conjugateEquiv_comp_counit` at the pullback--pushforward adjunction
of [Stacks, Tag 0096], the exact-support adjunction of [Stacks, Tag 0A75] and the
tensor--internal-Hom adjunction of [Stacks, Tag 03EO] at `𝒪_Z`; the threefold composite is
`pushforwardTensorPullbackAdjunction` at `𝒪_Z` by
`pushforwardTensorPullbackAdjunction_eq`. -/
theorem whiskerRight_conjugateEquiv_comp_counit_exactSupport
    (ζ : 𝟭 (_root_.SheafOfModules.{u} (structureSheafRing S.Z)) ⟶
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨(S.Z).presheaf, (S.Z).IsSheaf⟩).obj
        S.structureSheafModuleZ) :
    Functor.whiskerRight
          (Functor.whiskerLeft S.sheafHomExactSupport
            (conjugateEquiv (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ)
              Adjunction.id ζ))
          (modulePushforward S.i) ≫
        S.modulePushforwardSheafHomExactSupportAdjunction.counit =
      conjugateEquiv
        ((modulePullbackPushforwardAdjunction S.i).comp
          ((sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ).comp
            S.modulePushforwardSheafHomExactSupportAdjunction))
        Adjunction.id
        ((modulePullbackPushforwardAdjunction S.i).unit ≫
          Functor.whiskerLeft (modulePullback S.i)
            (Functor.whiskerRight ζ (modulePushforward S.i))) :=
  whiskerRight_conjugateEquiv_comp_counit (modulePullbackPushforwardAdjunction S.i)
    S.modulePushforwardSheafHomExactSupportAdjunction
    (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ) ζ

/-- **The trace of [Stacks, Tag 0A75], after the trivialisation of `ℰom_{𝒪_Z}(𝒪_Z, -)`, is a
conjugate for the adjunction the underived form of [Stacks, Tag 0E2I] is stated over.**  This is
the identity named as step (a) of the underived core of the remaining obligation of
[Stacks, Tag 0B4B] (see `StacksFrontier/AlgebraicGeometry/Duality/`
`EffectiveCartierDualTriangleComparison.lean`, "What is not done"), at the closed quotient
morphism itself: the right-hand side of the underived 0E2I isomorphism at the source `𝒪_Z` is
`i_* ℰom_{𝒪_Z}(𝒪_Z, ℰom(𝒪_Z, -))`, and trivialising the inner internal Hom and applying the trace
gives a transformation to `𝟭` which is the conjugate — for
`pushforwardTensorPullbackAdjunction` at `𝒪_Z` and the identity adjunction — of the unit
`𝟭 ⟶ i_* i^*` of [Stacks, Tag 0096] followed by the inverse left unitor on `Z`, whiskered into
`i^*` and `i_*`.

The inverse left unitor appears as the conjugate preimage of the trivialisation, which is what
it is by
`Stacks.SheafOfModules.InternalHom.internalHomSecondFunctorUnitIso_hom_eq_sheafTensor`; writing
it as the unitor here is not possible, for the reasons recorded on
`Stacks.SheafOfModules.InternalHom.whiskerRight_internalHomSecondFunctorUnitIso_comp_counit`. -/
theorem internalHomSecondFunctorUnitIso_whiskered_comp_counit :
    Functor.whiskerRight
          (Functor.whiskerLeft S.sheafHomExactSupport
            (internalHomSecondFunctorUnitIso S.Z.sheaf).hom) (modulePushforward S.i) ≫
        S.modulePushforwardSheafHomExactSupportAdjunction.counit =
      conjugateEquiv (S.pushforwardTensorPullbackAdjunction S.structureSheafModuleZ)
        Adjunction.id
        ((modulePullbackPushforwardAdjunction S.i).unit ≫
          Functor.whiskerLeft (modulePullback S.i)
            (Functor.whiskerRight
              ((conjugateEquiv (sheafTensorHomAdjunction S.Z.sheaf S.structureSheafModuleZ)
                  Adjunction.id).symm (internalHomSecondFunctorUnitIso S.Z.sheaf).hom)
              (modulePushforward S.i))) :=
  whiskerRight_internalHomSecondFunctorUnitIso_comp_counit_symm S.siteZ S.Z.sheaf
    (modulePullbackPushforwardAdjunction S.i) S.modulePushforwardSheafHomExactSupportAdjunction

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end

end
