module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ClosedImmersionBaseChangeStalkDiagram
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.KFlatResolvingDatum

/-!
# Tor-independent base change along a closed immersion

Consider a cartesian diagram of schemes

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

with `i` a closed immersion, and suppose `Z` and `X'` are Tor independent over `X`.  Then
`Ri'_* ∘ Lg^*` and `Lf^* ∘ Ri_*` agree as functors `D(𝒪_Z) ⟶ D(𝒪_{X'})`, the comparison being
the canonical derived base change map.

Invertibility of that map is detected on the derived stalks, where it becomes the base-change
comparison of two derived tensor products of local rings; Tor independence makes the latter
invertible.  This file carries out that pattern with the identification of the two sides on
derived stalks required **only at K-flat complexes**: every object of `D(𝒪_Z)` is the class of a
K-flat complex, and both sides of the identification are components of morphisms of functors, so
an identification at K-flat complexes propagates to every object.  The unconditional statement,
with the invertibility on derived stalks proved directly, is
`Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareAsIso`.

## Main definitions

* `Stacks.Cohomology.ClosedImmersionBaseChange.stalkBaseChangeNatTrans`: the derived stalk at
  `i' w` of the derived base change map, read through the source and target chains of
  comparisons, as a morphism of functors on `D(𝒪_Z)`.
* `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEqKFlat`: the stalkwise
  identification of that morphism with the ring-level comparison, demanded only at the classes
  of K-flat complexes.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIsoOfKFlatEq`: the
  isomorphism `Lf^* ∘ Ri_* ≅ Ri'_* ∘ Lg^*`, from that identification.

## Main results

* `Stacks.CategoryTheory.natTrans_app_eq_of_iso`: two morphisms of functors that agree at an
  object agree at every object isomorphic to it.
* `Stacks.Cohomology.ClosedImmersionBaseChange.exists_kFlatComplex_representative`: every object
  of the derived category of `𝒪_Y`-modules is isomorphic to the class of a K-flat complex.
* `Stacks.Cohomology.ClosedImmersionBaseChange.derivedStalkBaseChangeEq_iff_kFlat`: the
  stalkwise identification at every object of `D(𝒪_Z)` is equivalent to the identification at
  the classes of K-flat complexes.
* `Stacks.Cohomology.ClosedImmersionBaseChange.isIso_derivedBaseChangeSquare_of_kFlatEq`: the
  canonical morphism of functors `Ri_* ⋙ Lf^* ⟶ Lg^* ⋙ Ri'_*` is invertible, from the
  identification at K-flat complexes.

## Implementation notes

*Which spelling of the category of module sheaves.*  The complexes here are complexes of
`SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)`, the spelling the derived base change
map and `Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex` are written in.  The K-flat
representative statement of `Stacks.Duality.exists_kFlatComplex_iso` is the same assertion in
the `Z.Modules` spelling, over `Stacks.DerivedTensor.RingedSite`'s K-flatness; the two are
definitionally but not syntactically equal, and instance search runs at reducible transparency,
so the statement is reproved rather than transported.

*Why the stalkwise identification is restated through a morphism of functors.*  The two sides
of `Stacks.Cohomology.ClosedImmersionBaseChange.DerivedStalkBaseChangeEq` are, at each point
`w`, components of two morphisms of functors on `D(𝒪_Z)`, and that is what makes an
identification at one object of an isomorphism class suffice.  `stalkBaseChangeNatTrans` names
the first of them — the second is already a morphism of functors, namely `stalkComparison`
whiskered with the derived stalk at `g w` — and `stalkBaseChangeNatTrans_app` records that its
component is the composite that appears in `DerivedStalkBaseChangeEq`.  Going through that
component lemma is not cosmetic: supplying the equality to the propagation lemma directly asks
the kernel to see the composite and the component of the composite as one term inside a proof
of the full statement, and the check exhausts its budget.

## References

* [Stacks Project, Tag 06YF](https://stacks.math.columbia.edu/tag/06YF)
* [Stacks Project, Tag 0661](https://stacks.math.columbia.edu/tag/0661)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open CochainComplex.DerivedExtensionScalars
open RingTheory.TorIndependence
open Stacks.Cohomology.DerivedBaseChange

noncomputable section

namespace Stacks.CategoryTheory

universe v₁ v₂ w₁ w₂

/-- **Two morphisms of functors that agree at an object agree at every isomorphic object.**  The
two naturality squares at an isomorphism `A ≅ B` identify the component at `B` with the
component at `A` conjugated by it. -/
theorem natTrans_app_eq_of_iso {E : Type w₁} [Category.{v₁} E] {D : Type w₂} [Category.{v₂} D]
    {F G : E ⥤ D} (α β : F ⟶ G) {A B : E} (e : A ≅ B) (h : α.app A = β.app A) :
    α.app B = β.app B := by
  rw [← cancel_epi (F.map e.hom), α.naturality e.hom, β.naturality e.hom, h]

end Stacks.CategoryTheory

namespace Stacks.Cohomology.ClosedImmersionBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### K-flat representatives in the derived category of module sheaves -/

/-- **Every object of `D(𝒪_Y)` is isomorphic to the class of a K-flat complex.**  Every complex
of `𝒪_Y`-modules receives a quasi-isomorphism from a K-flat one, by Stacks 06YF, and a
quasi-isomorphism becomes invertible in the derived category. -/
theorem exists_kFlatComplex_representative (Y : RingedSpace.{u, u})
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ∃ P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Y P ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K) := by
  obtain ⟨P, q, hP, -, hq, -⟩ :=
    Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution Y
      (DerivedCategory.Q.objPreimage K)
  have hiso : IsIso (DerivedCategory.Q.map q) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso K⟩⟩

section Square

variable {Z' X' Z X : Scheme.{u}} {i' : Z' ⟶ X'} {g : Z' ⟶ Z} {f : X' ⟶ X} {i : Z ⟶ X}

/-! ### The derived stalk of the base change map, as a morphism of functors -/

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces in
/-- **The derived stalk of the base change map, as a morphism of functors.**  At a point `w` of
`Z'` the derived stalk at `i' w` of the derived base change map of Stacks 08HY, read through
`derivedStalkSourceIso` on the source and `derivedStalkTargetIso` on the target, is a morphism
of functors from `D(𝒪_Z)` to the derived category of modules over `𝒪_{X', i' w}`, between the
two sides of the comparison of Stacks 0661 at the local rings of the square. -/
def stalkBaseChangeNatTrans (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z') :
    AlgebraicGeometry.derivedStalkFunctor (g w) ⋙
        (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap (g w)).hom).mapDerivedCategory ⋙
          Lg w (ptEq sq w) ⟶
      AlgebraicGeometry.derivedStalkFunctor (g w) ⋙ Lh (g := g) w ⋙
        (ModuleCat.restrictScalars.{u, u, u} (i'.stalkMap w).hom).mapDerivedCategory :=
  let := isClosedImmersion_of_isPullback sq
  (derivedStalkSourceIso w (ptEq sq w)).inv ≫
    Functor.whiskerRight
      (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
        f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq))
      (AlgebraicGeometry.derivedStalkFunctor (i' w)) ≫
    (derivedStalkTargetIso w).hom

/-- The component of `stalkBaseChangeNatTrans` at a complex is the composite of the inverse of
the source chain, the derived stalk of the base change map, and the target chain. -/
theorem stalkBaseChangeNatTrans_app (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (w : Z')
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))) :
    letI := isClosedImmersion_of_isPullback sq
    (stalkBaseChangeNatTrans sq w).app K =
      (derivedStalkSourceIso w (ptEq sq w)).inv.app K ≫
        (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
          (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
            f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) K) ≫
        (derivedStalkTargetIso w).hom.app K :=
  rfl

/-! ### The stalkwise identification, demanded only at K-flat complexes -/

/-- **The stalkwise identification at K-flat complexes.**  For every point `w` of `Z'` and every
K-flat complex `P` of `𝒪_Z`-modules, the derived stalk at `i' w` of the derived base change map
of Stacks 08HY, read through the two chains of comparisons, is the comparison of Stacks 0661 at
the derived stalk of the class of `P` at `g w`.

This is `DerivedStalkBaseChangeEq` with its quantifier over objects of `D(𝒪_Z)` restricted to
the classes of K-flat complexes; `derivedStalkBaseChangeEq_iff_kFlat` says the restriction loses
nothing. -/
abbrev DerivedStalkBaseChangeEqKFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] : Prop :=
  let := isClosedImmersion_of_isPullback sq
  ∀ (w : Z') (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)) ℤ),
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex Z.toRingedSpace P →
      (derivedStalkSourceIso w (ptEq sq w)).inv.app (DerivedCategory.Q.obj P) ≫
          (AlgebraicGeometry.derivedStalkFunctor (i' w)).map
            (derivedBaseChangeMap g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
              f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq) (DerivedCategory.Q.obj P)) ≫
          (derivedStalkTargetIso w).hom.app (DerivedCategory.Q.obj P) =
        (stalkComparison sq w (ptEq sq w)).app
          ((AlgebraicGeometry.derivedStalkFunctor (g w)).obj (DerivedCategory.Q.obj P))

/-- **The stalkwise identification propagates off the K-flat complexes.**  Both sides of it are
components of morphisms of functors on `D(𝒪_Z)`, and every object of `D(𝒪_Z)` is isomorphic to
the class of a K-flat complex, so an identification there is an identification everywhere. -/
theorem derivedStalkBaseChangeEq_of_kFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (h : DerivedStalkBaseChangeEqKFlat sq) :
    DerivedStalkBaseChangeEq sq := by
  intro w K
  obtain ⟨P, hP, ⟨e⟩⟩ := exists_kFlatComplex_representative Z.toRingedSpace K
  rw [← stalkBaseChangeNatTrans_app]
  refine Stacks.CategoryTheory.natTrans_app_eq_of_iso (stalkBaseChangeNatTrans sq w)
    (Functor.whiskerLeft (AlgebraicGeometry.derivedStalkFunctor (g w))
      (stalkComparison sq w (ptEq sq w))) e ?_
  rw [stalkBaseChangeNatTrans_app]
  exact h w P hP

/-- The stalkwise identification at every object of `D(𝒪_Z)` and the stalkwise identification at
the classes of K-flat complexes are equivalent. -/
theorem derivedStalkBaseChangeEq_iff_kFlat (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] :
    DerivedStalkBaseChangeEq sq ↔ DerivedStalkBaseChangeEqKFlat sq :=
  ⟨fun h w P _ => h w (DerivedCategory.Q.obj P), derivedStalkBaseChangeEq_of_kFlat sq⟩

/-! ### Tor-independent base change along a closed immersion -/

/-- **The canonical morphism of functors `Ri_* ⋙ Lf^* ⟶ Lg^* ⋙ Ri'_*` of Stacks 08HY is
invertible**, for a cartesian square with `i` a closed immersion and `Z`, `X'` Tor independent
over `X`, from the stalkwise identification at K-flat complexes. -/
theorem isIso_derivedBaseChangeSquare_of_kFlatEq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (h : DerivedStalkBaseChangeEqKFlat sq) :
    IsIso (derivedBaseChangeSquare g.toLRSHom.toShHom i'.toLRSHom.toShHom i.toLRSHom.toShHom
      f.toLRSHom.toShHom (comp_toShHom_of_isPullback sq)) :=
  isIso_derivedBaseChangeSquare_of_eq sq htor (derivedStalkBaseChangeEq_of_kFlat sq h)

/-- **Tor-independent base change along a closed immersion.**  For a cartesian square with `i` a
closed immersion and `Z`, `X'` Tor independent over `X`, the functors `Lf^* ∘ Ri_*` and
`Ri'_* ∘ Lg^*` from `D(𝒪_Z)` to `D(𝒪_{X'})` are isomorphic, by the canonical derived base change
map of Stacks 08HY.  The stalkwise identification of that map with the comparison of Stacks 0661
is carried as a hypothesis, and is demanded only at K-flat complexes; the unconditional
statement is `Stacks.Cohomology.ClosedImmersionBaseChange.derivedBaseChangeSquareIso`. -/
def derivedBaseChangeSquareIsoOfKFlatEq (sq : IsPullback i' g f i)
    [AlgebraicGeometry.IsClosedImmersion i] (htor : AlgebraicGeometry.TorIndependent i f)
    (h : DerivedStalkBaseChangeEqKFlat sq) :
    Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward i.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback f.toLRSHom.toShHom ≅
      Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom ⋙
        Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward
          i'.toLRSHom.toShHom :=
  derivedBaseChangeSquareIsoOfEq sq htor (derivedStalkBaseChangeEq_of_kFlat sq h)

end Square

end Stacks.Cohomology.ClosedImmersionBaseChange

end

end
