module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsZeroRelations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalizedPullbackQuasicoherent
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback along a morphism of ringed topoi preserves finite local freeness

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `F` be a sheaf
of `O_D`-modules which is finite locally free, Stacks 03DL(2).  Stacks 03DO, for that clause,
asserts that the pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6(2) is again finite locally
free.  This file proves it, for an arbitrary morphism of ringed topoi and with no hypothesis on
the two sites beyond the ones its inputs carry.

## The route

Finite freeness looks as though it could not travel along `f⁻¹`: "the map `O^n ⟶ F` is an
isomorphism" is not a geometric statement, and the usual repair — carrying the inverse as a
section of an internal Hom — would need a comparison `f⁻¹𝓗om(F, G) ⟶ 𝓗om(f⁻¹F, f⁻¹G)` compatible
with evaluation, which this development does not have.  **No such comparison is needed: finite
freeness is finite presentation with no relations**, and the machinery of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackPresentationAssembly` is already
parameterized by the number of relations.  The route is therefore the one that file takes for the
clause 03DL(7), with the relation count fixed at `0` throughout and the index of the family of
data sheaves accordingly `ℕ` rather than `ℕ × ℕ`:

1. `Stacks.Sheaves.LocalGeneration.jointlyLocallyInhabited_presDataSheaf_zero`: finite local
   freeness of `F` makes the family `n ↦ presDataSheaf F n 0` jointly locally inhabited;
2. `Stacks.Topos.exists_cover_inverseImage_sections`: joint local inhabitedness transports along
   `f⁻¹`, so every object of the source site is covered by objects carrying a section of
   `f⁻¹(presDataSheaf F n 0)` for some `n`;
3. `Stacks.Sheaves.PresentationTransport.isPresentationData_pullback`: such a section is
   presentation data for `f⁻¹F`, with the same `n` and the same relation count `0`;
4. `Stacks.Sheaves.LocalGeneration.isFiniteFree_of_isPresentationData_zero`: data with no
   relations makes the restriction of `f⁻¹F` finite free;
5. `Stacks.Sheaves.FinitePresentation.isFiniteFree_extendScalarsOver`: extension of scalars along
   `f⁻¹O_D ⟶ O_C` carries finite free of rank `n` to finite free of rank `n`.

Steps 2 and 3 are the two expensive ones and are used unchanged: nothing in
`ToposPullbackPresentationData`, `ToposPullbackPresentationEncode` or
`ToposPullbackPresentationTransport` is rewritten, and no colimit over the index of the family is
formed.

## Main results

* `Stacks.Sheaves.FinitePresentation.isFiniteFree_extendScalarsOver`: extension of scalars on a
  slice site preserves finite freeness. This is `Stacks.Sheaves.LocalizedPullback.isFiniteFree_map`
  at the left adjoint `extendScalarsOver`, whose unit comparison and whose commutation with
  restriction to the slice are already recorded.
* `Stacks.Sheaves.PresentationTransport.exists_cover_isFiniteFree_inverseImage`: **the
  inverse-image half.**  Every object of the source site has a covering on whose members the
  inverse image of a finite locally free sheaf of modules is finite free.
* `Stacks.Sheaves.FinitePresentation.isFiniteLocallyFreeOnSite_pullbackModules`: **Stacks 03DO
  for the clause 03DL(2)**, the pullback of a finite locally free sheaf of modules along a
  morphism of ringed topoi is finite locally free.

## Implementation notes

The only other statements of Stacks 03DO(2) in this development are
`Stacks.Sheaves.LocalizedPullback.isFiniteLocallyFreeOnSite_pullbackTopos`, for a morphism of
ringed *sites* presented by a left exact continuous functor with all universes collapsed, and
`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_etaleModulePullback_iff`, for an étale
morphism of algebraic spaces.  Neither covers an arbitrary morphism of ringed topoi, which is what
is proved here; no notion is introduced and nothing is narrowed.

The covering family demanded by `SheafOfModules.IsFiniteLocallyFreeOnSite` is indexed by a type
in `Type (max u v)`, while the transport produces a covering *sieve*; the two are reconciled by
the index `Σ W, {g : W ⟶ U // T g}`, exactly as in
`Stacks.Sheaves.FinitePresentation.pullbackModules_isFinitePresentationOnSite`.

## References

* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sheaves.FinitePresentation

/-! ### Extension of scalars on a slice site preserves finite freeness -/

section ExtendScalarsOverFree

open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.LocalGeneration

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A₁ A₂ : Cᵒᵖ ⥤ CommRingCat.{w}} (θ : A₁ ⟶ A₂)
  (h₁ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₁))
  (h₂ : Presheaf.IsSheaf J (Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf A₂))
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Extension of scalars transports finite freeness through restriction to a slice site.**  A
finite free restriction `M|_V` gives a finite free `(A₂ ⊗_{A₁} M)|_V`, of the same rank:
extension of scalars on the slice site is a left adjoint, hence preserves the coproduct cofan,
and it carries the structure sheaf to the structure sheaf and commutes with restriction to the
slice.

This is the finite-freeness companion of
`Stacks.Sheaves.FinitePresentation.isFinite_presentationExtendScalarsOver`, and it is
`Stacks.Sheaves.LocalizedPullback.isFiniteFree_map` at `extendScalarsOver`: that statement needs
exactly colimit preservation, a unit comparison and an identification of the image, which
`preservesColimitsOfSize_extendScalarsOver`, `extendScalarsOverUnitIso` and
`extendScalarsOverObjIso` supply. -/
theorem isFiniteFree_extendScalarsOver
    (M : _root_.SheafOfModules.{w} (commRingSheaf J A₁ h₁)) (V : C)
    (hM : _root_.SheafOfModules.IsFiniteFree ((commRingSheaf J A₁ h₁).over V) (M.over V)) :
    _root_.SheafOfModules.IsFiniteFree ((commRingSheaf J A₂ h₂).over V)
      (((extendScalars J θ h₁ h₂).obj M).over V) := by
  have : PreservesColimitsOfSize.{0, 0} (extendScalarsOver θ h₁ h₂ V) :=
    preservesColimitsOfSize_shrink _
  exact Stacks.Sheaves.LocalizedPullback.isFiniteFree_map (extendScalarsOver θ h₁ h₂ V)
    (extendScalarsOverUnitIso θ h₁ h₂ V).symm (extendScalarsOverObjIso θ h₁ h₂ M V) hM

end ExtendScalarsOverFree

end Stacks.Sheaves.FinitePresentation

/-! ### The inverse-image half -/

namespace Stacks.Sheaves.PresentationTransport

open Stacks.Sheaves.LocalGeneration Stacks.Topos

universe v u v' u' w w'

section Assembly

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{w})] [K.HasSheafCompose (forget RingCat.{w'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [K.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [∀ Z : C, HasWeakSheafify (J.over Z) AddCommGrpCat.{w}]
  [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ Z : D, HasWeakSheafify (K.over Z) AddCommGrpCat.{w'}]
  [∀ Z : D, (K.over Z).WEqualsLocallyBijective AddCommGrpCat.{w'}]

/-- **The inverse-image half of Stacks 03DO for the clause 03DL(2).**  If `F` is a finite locally
free sheaf of `O`-modules on the target site, then every object `U` of the source site has a
covering on whose members the inverse image `f⁻¹F` of Stacks 03D2 is finite free.

The covering is the one `Stacks.Topos.exists_cover_inverseImage_sections` produces for the family
`n ↦ presDataSheaf F n 0` of sheaves of rank-`n` trivializations of `F`, so no colimit over the
index `ℕ` of that family is formed. -/
theorem exists_cover_isFiniteFree_inverseImage
    (f : MorphismOfTopoi (Sheaf J (Type w)) (Sheaf K (Type w')))
    (R : Sheaf K RingCat.{w'}) (P : ToposPullback.PullbackModuleData J K f R)
    (M : SheafOfModules.{w'} R) (hM : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite M) (U : C) :
    ∃ T : J.Cover U, ∀ (V : C) (g : V ⟶ U), T g →
      _root_.SheafOfModules.IsFiniteFree (P.ring.over V) ((P.moduleFunctor.obj M).over V) := by
  obtain ⟨T, hT⟩ := exists_cover_inverseImage_sections f
    (fun n : ℕ => presDataSheaf M n 0) (jointlyLocallyInhabited_presDataSheaf_zero M hM) U
  refine ⟨T, fun V g hg => ?_⟩
  obtain ⟨n, ⟨p⟩⟩ := hT V g hg
  exact isFiniteFree_of_isPresentationData_zero (P.moduleFunctor.obj M) _ _
    (isPresentationData_pullback f R P M (presentationDataSheaf R M n 0) p)

end Assembly

end Stacks.Sheaves.PresentationTransport

/-! ### Stacks 03DO for the clause 03DL(2) -/

namespace Stacks.Sheaves.FinitePresentation

open AlgebraicGeometry Stacks.Sheaves.PresentationTransport
open Stacks.Sheaves.RingedToposModules Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.ToposPushforward

universe v u v' u' w

/-- **Stacks 03DO for the clause 03DL(2): pullback preserves finite local freeness.**  The
pullback `f^*F = O_C ⊗_{f⁻¹O_D} f⁻¹F` of Stacks 03D6(2) of a finite locally free sheaf of
`O_D`-modules along a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is finite
locally free.

The two halves are
`Stacks.Sheaves.PresentationTransport.exists_cover_isFiniteFree_inverseImage`, which produces a
covering of each object of the source site on whose members `f⁻¹F` is finite free, and
`Stacks.Sheaves.FinitePresentation.isFiniteFree_extendScalarsOver`, which carries that across
extension of scalars along `f⁻¹O_D ⟶ O_C`. -/
@[stacks 03DO "finite_locally_free",
  ega "0 5.4.5" "locally free clause",
  ega "II 6.4.8" "more general",
  ega "III 7.7.9" "partial"]
theorem isFiniteLocallyFreeOnSite_pullbackModules {X : RingedTopos.{v, u, w}}
    {Y : RingedTopos.{v', u', w}}
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w})]
    [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [HasWeakSheafify X.J AddCommGrpCat.{w}] [HasWeakSheafify Y.J AddCommGrpCat.{w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ Z : X.C, HasWeakSheafify (X.J.over Z) AddCommGrpCat.{w}]
    [∀ Z : Y.C, HasWeakSheafify (Y.J.over Z) AddCommGrpCat.{w}]
    [∀ Z : X.C, (X.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ Z : Y.C, (Y.J.over Z).WEqualsLocallyBijective AddCommGrpCat.{w}]
    (f : RingedToposModules.RingedToposHom X Y)
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hF : _root_.SheafOfModules.IsFiniteLocallyFreeOnSite F) :
    _root_.SheafOfModules.IsFiniteLocallyFreeOnSite (f.pullbackModules.obj F) := by
  intro U
  obtain ⟨T, hT⟩ := exists_cover_isFiniteFree_inverseImage f.toToposHom
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
    (pullbackModule X.J Y.J f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) F hF U
  refine ⟨Σ W : X.C, {g : W ⟶ U // T.1 g}, fun i => i.1, fun i => i.2.1, ?_, fun i => ?_⟩
  · refine X.J.superset_covering (fun Z g hg => ?_) T.2
    exact (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨Z, g, hg⟩, 𝟙 Z, (Category.id_comp g).symm⟩
  · exact isFiniteFree_extendScalarsOver (fSharpCommRing f)
      (inverseImageRingSheaf f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).property
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property
      ((inverseImageModules f.toToposHom
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj F) i.1
      (hT i.1 i.2.1 i.2.2)

end Stacks.Sheaves.FinitePresentation

end
