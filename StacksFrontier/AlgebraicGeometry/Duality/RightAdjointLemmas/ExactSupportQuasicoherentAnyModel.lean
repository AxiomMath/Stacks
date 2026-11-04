module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportQuasicoherent
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardAnyModel
public import StacksCore.Tactic.StacksAttribute

/-!
# Part (1) of Tag 0A78, at an arbitrary derived category

Let `i : Z ⟶ W` be a pseudo-coherent closed immersion of schemes. Part (1) of
[Stacks, Tag 0A78] — that the right derived functor `R ℰom(𝒪_Z, -)` of sheaf Hom with exact
support carries `D⁺_QCoh(𝒪_W)` into `D⁺_QCoh(𝒪_Z)` — is proved in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherent.lean` at
`CategoryTheory.HasDerivedCategory.standard`. `HasDerivedCategory` carries the localized category
as *data*, so that statement says nothing about the locally small model
`SheafOfModules.hasDerivedCategory`, which is the model at which `D(𝒪_W)` has the direct sums
Brown representability ([Stacks, Tag 0A8G]) asks for and therefore the only one at which the
existence of `i^!` ([Stacks, Tag 0A9E]) is available. This file removes the pin.

The route is the one
`StacksFrontier/AlgebraicGeometry/Duality/DerivedPushforward/UniformBoundAnyModel.lean` takes for
part (2) of [Stacks, Tag 08D5] and
`StacksFrontier/AlgebraicGeometry/QuasiCoherent/Coherator/AffinePushforwardAnyModel.lean` for part
(1) of that tag: the statement is first re-expressed with **no derived category in it at all** —
for `s : K ⟶ J` a K-injective resolution of a complex with quasi-coherent cohomology bounded
below, the complex `ℰom(𝒪_Z, J)`, which computes `R ℰom(𝒪_Z, K)`, has quasi-coherent cohomology
sheaves and they vanish in low degrees — and then read back at an arbitrary
`[HasDerivedCategory.{w}]`, where
`Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso` identifies `R ℰom(𝒪_Z, E)` with the
object represented by `ℰom(𝒪_Z, J)`.

A statement about complexes and quasi-isomorphisms only has no derived category in it, so it is
model-agnostic and crosses for free; that is why the spine behind the standard-model statement —
part (1) of [Stacks, Tag 0A6H] and [Stacks, Tag 06Z0], a dozen files one of which would have to
be split — does not have to be re-pinned.

## Main definitions

* `Stacks.Duality.AnyModel.derivedSheafHomExactSupport` and
  `Stacks.Duality.AnyModel.derivedSheafHomExactSupportComparison` — `R ℰom(𝒪_Z, -)` and its
  comparison map from the underived functor, at an arbitrary chosen model of the two derived
  categories. These are
  `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
  and its comparison with the choice of derived category a binder rather than a term.
* `Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso` — `R ℰom(𝒪_Z, K)` is represented by
  the complex `ℰom(𝒪_Z, J)` for a K-injective resolution `K ⟶ J`.

## Main results

* `Stacks.Duality.exists_isZero_isQuasicoherent_homology_sheafHomExactSupport` —
  **part (1) of [Stacks, Tag 0A78] with no derived category in the statement.**
* `Stacks.Duality.AnyModel.isBoundedBelow_isQuasicoherent_derivedSheafHomExactSupport_obj` — the
  same at an arbitrary chosen model of the two derived categories, in the elementary form
  (vanishing in low degrees, and quasi-coherence of every cohomology sheaf).

## Implementation notes

**No `@[stacks 0A78]` attribute is placed here.** The tag has two parts and its covering set is
the pair of them; both are carried by
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportQuasicoherent.lean`, and
part (2) genuinely uses the standard model — it runs [Stacks, Tag 06Z0] through
`AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful`. What is transported here is
part (1) alone, and it is transported for one consumer, [Stacks, Tag 0A9X]; the attribute stays
where the covering set is.

**`attribute [local instance 10000] HasDerivedCategory.standard`, not a plain `local instance`.**
The import closure carries the locally small `SheafOfModules.hasDerivedCategory` and
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` as global instances; at equal priority
instance search picks those, which would make the statement of the standard-model section mention
a model its input is not stated at. The attribute is scoped to `section Standard`, so the
arbitrary-model statements after it are unaffected.

**The derived functor is rebuilt here rather than imported.**
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
resolves its `HasDerivedCategory` instance at declaration time, so the functor it names is pinned
to the standard model; the abbreviation below is the same total right derived functor with the
model left as a binder, and the K-injective criterion of [Stacks, Tag 070K] applies to it because
sheaves of modules form a Grothendieck abelian category and therefore admit functorial K-injective
resolutions ([Stacks, Tag 079P]). This is the same rebuilding that
`Stacks.Duality.LocallySmall.derivedSheafHomExactSupport` performs at the locally small model.

**The conclusion is in the elementary form, not as `derivedCategoryBPlus`.** Membership in
`D⁺_QCoh` is `DerivedCategoryB.derivedCategoryBPlus` applied to
`SheafOfModules.isQuasicoherent`, which is stated over the spelling
`AlgebraicGeometry.Scheme.Modules` of the category of `𝒪_W`-modules, while sheaf Hom with exact
support is stated over `SheafOfModules (structureSheafRing _)`. Those are
definitionally equal but carry separately declared instances, and a free `[HasDerivedCategory.{w}]`
binder is found only for the spelling it is written in. Stating the arbitrary-model conclusion as
a vanishing range together with quasi-coherence of each cohomology sheaf keeps the whole statement
in the second spelling; the consumer, which works at the locally small model where the two global
instances agree by `rfl`, repackages it.

## References

* [Stacks Project, Tag 0A78](https://stacks.math.columbia.edu/tag/0A78)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingedSpaceModuleAdjunction

universe w u

namespace Stacks.Duality.AnyModel

/-! ### `R ℰom(𝒪_Z, -)` at an arbitrary model -/

section

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.X))]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing S.Z))]

/-- Sheaf Hom with exact support has a pointwise total right derived functor at any chosen model
of the target derived category: sheaves of modules form a Grothendieck abelian category, so every
complex of them admits a quasi-isomorphism into a K-injective complex, and that criterion
([Stacks, Tag 070K]) is model-free. -/
instance hasPointwiseRightDerivedFunctor_sheafHomExactSupport :
    (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)) :=
  Stacks.DerivedFunctor.hasPointwiseRightDerivedFunctor_of_exists_isKInjective _
    (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)

/-- **`R ℰom(𝒪_Z, -) : D(𝒪_X) ⥤ D(𝒪_Z)` at an arbitrary chosen model of the two derived
categories.** This is
`RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupport`
with the choice of derived category a binder rather than a term. -/
abbrev derivedSheafHomExactSupport :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) :=
  (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-- The canonical map from sheaf Hom with exact support to its right derived functor, at an
arbitrary chosen model of the two derived categories. -/
abbrev derivedSheafHomExactSupportComparison :
    S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSheafHomExactSupport.{w} S :=
  (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing S.X)) (ComplexShape.up ℤ))

/-- A K-injective complex computes the right derived functor of sheaf Hom with exact support at
any chosen model: on it the canonical comparison `ℰom(𝒪_Z, J) ⟶ R ℰom(𝒪_Z, J)` is invertible.
This is the second half of the K-injective criterion of [Stacks, Tag 070K], whose hypothesis —
the existence of K-injective resolutions in the source — is model-free. -/
theorem isIso_derivedSheafHomExactSupportComparison_app_of_isKInjective
    (J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ) (hJ : J.IsKInjective) :
    IsIso ((derivedSheafHomExactSupportComparison.{w} S).app
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
        (ComplexShape.up ℤ)).obj J)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (S.sheafHomExactSupport.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K => Stacks.DerivedFunctor.exists_quasiIso_isKInjective K)).2
    DerivedCategory.Qh (derivedSheafHomExactSupport.{w} S)
    (derivedSheafHomExactSupportComparison.{w} S) J hJ

/-- **`R ℰom(𝒪_Z, K)` is the termwise sheaf Hom with exact support of a K-injective resolution of
`K`.** Given a quasi-isomorphism `s : K ⟶ J` into a K-injective complex, the object
`R ℰom(𝒪_Z, K)` of the chosen derived category of `𝒪_Z`-modules is the one represented by the
complex `ℰom(𝒪_Z, J)`: the comparison map is invertible at `J`, and `s` becomes invertible in the
derived category of `𝒪_X`-modules. -/
def derivedSheafHomExactSupportObjIso
    {K J : CochainComplex (SheafOfModules.{u} (structureSheafRing S.X)) ℤ} (s : K ⟶ J)
    (hJ : J.IsKInjective) (hs : QuasiIso s) :
    (derivedSheafHomExactSupport.{w} S).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing S.X))
          (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj ((S.sheafHomExactSupport.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) :=
  have := (Stacks.SmallDerivedCategory.isIso_Qh_map_quotient_map_iff s).2 hs
  have := isIso_derivedSheafHomExactSupportComparison_app_of_isKInjective.{w} S J hJ
  (derivedSheafHomExactSupport.{w} S).mapIso (asIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map s))) ≪≫
    (asIso ((derivedSheafHomExactSupportComparison.{w} S).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj J))).symm ≪≫
    (Stacks.SmallDerivedCategory.mapHomotopyCategoryCompQhFactors S.sheafHomExactSupport).app J

end

/-- The cohomology sheaves of the object of `D(𝒪_X)` represented by a complex `K` are the
cohomology sheaves of `K`, at any chosen model of the derived category. -/
def homologyQhObjIso {A : Type (u + 1)} [Category.{u} A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : CochainComplex A ℤ) (n : ℤ) :
    (DerivedCategory.homologyFunctor A n).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ≅
      K.homology n :=
  (DerivedCategory.homologyFunctor A n).mapIso
      ((DerivedCategory.quotientCompQhIso A).app K) ≪≫
    (DerivedCategory.homologyFunctorFactors A n).app K

end Stacks.Duality.AnyModel

namespace Stacks.Duality

/-! ### Part (1) of Tag 0A78 with no derived category in the statement -/

section Standard

/-- Vanishing in low degrees and a closed-under-isomorphism property of a family of objects
transfer along a termwise isomorphism of the family. -/
private theorem isBoundedBelow_and_prop_of_iso {A : Type*} [Category A] [HasZeroMorphisms A]
    (P : ObjectProperty A) [P.IsClosedUnderIsomorphisms] {X Y : ℤ → A} (e : ∀ n, X n ≅ Y n)
    (h : (∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (X n)) ∧ ∀ n, P (X n)) :
    (∃ b : ℤ, ∀ n : ℤ, n < b → IsZero (Y n)) ∧ ∀ n, P (Y n) :=
  ⟨h.1.imp fun _ hb n hn => (hb n hn).of_iso (e n).symm, fun n => P.prop_of_iso (e n) (h.2 n)⟩

attribute [local instance 10000] HasDerivedCategory.standard

/-- **Part (1) of [Stacks, Tag 0A78] with no derived category in the statement.** Let
`i : Z ⟶ W` be a pseudo-coherent closed immersion of schemes, let `K` be a complex of
`𝒪_W`-modules whose cohomology sheaves are quasi-coherent and vanish in degrees `< b`, and let
`s : K ⟶ J` be a quasi-isomorphism into a K-injective complex. Then the cohomology sheaves of
`ℰom(𝒪_Z, J)` — the complex computing `R ℰom(𝒪_Z, K)` — are quasi-coherent, and they vanish in
degrees `< b'` for some `b'`.

This is `AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus` read at
the object represented by `K`. That object lies in `D⁺_QCoh(𝒪_W)`, its image lies in
`D⁺_QCoh(𝒪_Z)`, and `Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso` identifies that
image with the object represented by `ℰom(𝒪_Z, J)`. Separating the statement from the derived
category is what lets it be used at a model other than
`CategoryTheory.HasDerivedCategory.standard`; see the module documentation. -/
theorem exists_isZero_isQuasicoherent_homology_sheafHomExactSupport
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i] (hi : PseudoCoherent i)
    {K J : CochainComplex (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) ℤ}
    (hqc : ∀ n : ℤ, (K.homology n).IsQuasicoherent)
    (b : ℤ) (hb : ∀ n : ℤ, n < b → IsZero (K.homology n))
    (s : K ⟶ J) (hJ : J.IsKInjective) (hs : QuasiIso s) :
    (∃ b' : ℤ, ∀ n : ℤ, n < b' →
        IsZero (((Functor.mapHomologicalComplex
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).sheafHomExactSupport
          (ComplexShape.up ℤ)).obj J).homology n)) ∧
      ∀ n : ℤ, (((Functor.mapHomologicalComplex
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).sheafHomExactSupport
        (ComplexShape.up ℤ)).obj J).homology n).IsQuasicoherent := by
  set S := Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i with hS
  set E := DerivedCategory.Qh.obj ((HomotopyCategory.quotient
    (SheafOfModules.{u} (structureSheafRing W.toRingedSpace)) (ComplexShape.up ℤ)).obj K) with hE
  obtain ⟨hbdd, hcoh⟩ := isBoundedBelow_and_prop_of_iso
    (SheafOfModules.isQuasicoherent W.ringCatSheaf) (fun n => (AnyModel.homologyQhObjIso K n).symm)
    ⟨⟨b, hb⟩, hqc⟩
  have hQC := AlgebraicGeometry.Scheme.derivedSheafHomExactSupport_mem_derivedCategoryBPlus
    i hi E ⟨hbdd, hcoh⟩
  have eZ : ∀ n : ℤ, (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) n).obj
          (S.derivedSheafHomExactSupport.obj E) ≅
      ((S.sheafHomExactSupport.mapHomologicalComplex (ComplexShape.up ℤ)).obj J).homology n :=
    fun n => (DerivedCategory.homologyFunctor _ n).mapIso
        (AnyModel.derivedSheafHomExactSupportObjIso S s hJ hs) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _
  exact isBoundedBelow_and_prop_of_iso (SheafOfModules.isQuasicoherent Z.ringCatSheaf) eZ hQC

end Standard

/-! ### Part (1) of Tag 0A78 at an arbitrary model -/

namespace AnyModel

/-- **Part (1) of [Stacks, Tag 0A78] at an arbitrary chosen model of the two derived
categories.** Let `i : Z ⟶ W` be a pseudo-coherent closed immersion of schemes and let `E` be an
object of `D(𝒪_W)` whose cohomology sheaves are quasi-coherent and vanish in low degrees. Then the
cohomology sheaves of `R ℰom(𝒪_Z, E)` are quasi-coherent and vanish in low degrees; that is,
`R ℰom(𝒪_Z, -)` carries `D⁺_QCoh(𝒪_W)` into `D⁺_QCoh(𝒪_Z)`.

Every object of the derived category is represented by a complex `K`, and
`Stacks.Duality.AnyModel.derivedSheafHomExactSupportObjIso` identifies `R ℰom(𝒪_Z, E)` with the
object represented by `ℰom(𝒪_Z, J)` for a K-injective resolution `K ⟶ J`; the cohomology sheaves
of that complex are quasi-coherent and vanish in low degrees by the model-free
`Stacks.Duality.exists_isZero_isQuasicoherent_homology_sheafHomExactSupport`. -/
theorem isBoundedBelow_isQuasicoherent_derivedSheafHomExactSupport_obj
    {Z W : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i] (hi : PseudoCoherent i)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z))]
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)))
    (hcoh : ∀ n : ℤ, ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) n).obj E).IsQuasicoherent)
    (b : ℤ) (hb : ∀ n : ℤ, n < b → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) n).obj E)) :
    (∃ b' : ℤ, ∀ n : ℤ, n < b' → IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z)) n).obj
          ((derivedSheafHomExactSupport.{w}
            (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i)).obj E))) ∧
      ∀ n : ℤ, ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z)) n).obj
          ((derivedSheafHomExactSupport.{w}
            (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i)).obj
              E)).IsQuasicoherent := by
  set K := DerivedCategory.Q.objPreimage E with hK
  let eE : DerivedCategory.Qh.obj ((HomotopyCategory.quotient
      (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X))
        (ComplexShape.up ℤ)).obj K) ≅ E :=
    (DerivedCategory.quotientCompQhIso (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X))).app K ≪≫
      DerivedCategory.Q.objObjPreimageIso E
  obtain ⟨⟨b, hKb⟩, hKcoh⟩ := isBoundedBelow_and_prop_of_iso
    (SheafOfModules.isQuasicoherent W.ringCatSheaf)
    (fun n => ((DerivedCategory.homologyFunctor _ n).mapIso eE).symm ≪≫ homologyQhObjIso K n)
    ⟨⟨b, hb⟩, hcoh⟩
  obtain ⟨J, s, hJ, hs⟩ :=
    Stacks.DerivedFunctor.exists_quasiIso_isKInjective
      (A := SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).X)) K
  obtain ⟨⟨b', hb'⟩, hqc'⟩ :=
    exists_isZero_isQuasicoherent_homology_sheafHomExactSupport i hi hKcoh b hKb s hJ hs
  have eZ : ∀ n : ℤ, (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing
      (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).Z)) n).obj
          ((derivedSheafHomExactSupport.{w}
            (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i)).obj E) ≅
      ((Functor.mapHomologicalComplex
        (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i).sheafHomExactSupport
        (ComplexShape.up ℤ)).obj J).homology n := fun n =>
    (DerivedCategory.homologyFunctor _ n).mapIso
        ((derivedSheafHomExactSupport.{w}
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i)).mapIso eE).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso
        (derivedSheafHomExactSupportObjIso.{w}
          (Stacks.ClosedImmersion.closedQuotientOfClosedImmersion i) s hJ hs) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _
  exact isBoundedBelow_and_prop_of_iso (SheafOfModules.isQuasicoherent Z.ringCatSheaf)
    (fun n => (eZ n).symm) ⟨⟨b', hb'⟩, hqc'⟩

end AnyModel

end Stacks.Duality

end
