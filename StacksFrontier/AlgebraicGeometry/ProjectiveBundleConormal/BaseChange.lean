module

public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.CanonicalMap
public import StacksFrontier.AlgebraicGeometry.Chow.GenuineChern.BundleBaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSheaf
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.ConormalSource
public import StacksFrontier.AlgebraicGeometry.Thickenings.ConormalSequenceIdealForm
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the canonical conormal map of a section of a projective bundle

Let `g : X' ⟶ X`, let `ℰ` be quasi-coherent on `X` and `ℰ'` quasi-coherent on `X'` with
`hE : ℰ' ≅ g^*ℰ`. Write `π : 𝐏(ℰ) ⟶ X` and `π' : 𝐏(ℰ') ⟶ X'` for the two projections and
`h : 𝐏(ℰ') ⟶ 𝐏(ℰ)` for `Stacks.ProjectiveBundle.baseChangeHom`, whose square with `π`, `π'`
and `g` is cartesian. Let `σ` be a section of `π` classifying an invertible quotient `Q` and
`σ'` a section of `π'` classifying `Q'`, lying over `σ` in the sense `σ' ≫ h = g ≫ σ`.

Tag 0B3V's last sentence says that both the bijection and the isomorphism of the tag are
compatible with base change. The bijection half is
`Stacks.RelativeProj.sectionsMap_sectionBaseChange`. This file is about the isomorphism half:
the commuting square

```
  g^*(ker q ⊗ L^{⊗ -1})  --->  ker q' ⊗ (L')^{⊗ -1}
          |                            |
          |                            |
          v                            v
      g^* 𝒞_{σ(X)/𝐏(ℰ)}   --->    𝒞_{σ'(X')/𝐏(ℰ')}
```

whose horizontal maps are `Stacks.ProjectiveBundleConormal.conormalCanonicalMap` at the two
bundles, whose left vertical is `Stacks.Divisors.conormalSourceBaseChange` and whose right
vertical is built here.

## Main definitions

* `Stacks.ClosedImmersion.pullbackCompNatIso`: the identification `f^*j^* ≅ i^*k^*` furnished by
  a commuting square `i ≫ k = f ≫ j`, as a natural isomorphism of functors. Its components are
  `Stacks.ClosedImmersion.pullbackCompIso`, which was only ever available pointwise, so nothing
  could be moved past it; this is what supplies
  `Stacks.ClosedImmersion.pullbackCompIso_naturality`.
* `Stacks.Conormal.conormalBaseChangeMap`: **the canonical map `f^*𝒞_j ⟶ 𝒞_i` attached to a
  commuting square of immersions**, at the scheme spelling and at
  `Stacks.Conormal.conormalSheaf`. This is `Stacks.ClosedImmersion.conormalSheafMap` read
  through `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` at both ends; it is the right
  vertical of the square above, and before this file the development had no map of conormal
  sheaves of schemes attached to a square at all.

## Main results

* `Stacks.ClosedImmersion.pullbackCompIso_naturality`: a morphism of modules on `W'` may be
  moved past the square's identification.
* `Stacks.ClosedImmersion.lift_comp_idealSheafMap`: **a morphism compatible with two maps into
  the structure sheaves lifts to the ideal sheaves.** This is the step that uses the
  monomorphism pinning a factorization through an ideal sheaf, and it is available only before
  any further pullback.
* `Stacks.Conormal.conormalBaseChangeMap_eq`: the right vertical, spelled out.
* `Stacks.ProjectiveBundleConormal.idealSheafLift_baseChange_of_twisted`: **the lift
  coherence.** An identification `Φ` of `h^*((π^*ker q) ⊗ 𝒪(-1))` with its primed counterpart
  that carries the base change of the untwisted tautological map `ṽ` to `ṽ'` carries the base
  change of `Stacks.ProjectiveBundleConormal.idealSheafLift` to the primed lift, over
  `Stacks.ClosedImmersion.idealSheafMap`. `Φ` is a variable and is not assumed invertible.
* `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_idealSheafLift`,
  `idealSheafLift_baseChange_of_source` and **`conormalCanonicalMap_baseChange_of_source`**: the
  clause's square commutes as soon as there is a `Φ` as above which additionally agrees, after
  `σ'^*` and across the square, with `Stacks.Divisors.conormalSourceBaseChange`. The two
  identifications `𝒞 ≅ σ^*ℐ(σ)` of
  `Stacks.CartierConormal.conormalSheafIsoPullbackSelf`, the functoriality of `g^*`, the passage
  of `g^*σ^*(lift)` across the square, and the monomorphism pinning a factorization through an
  ideal sheaf are all discharged.

## What is still owed, precisely

`conormalCanonicalMap_baseChange_of_source` takes three hypotheses and **none of them is proved
here**; all three are proved downstream, and the clause with no hypothesis beyond the data of the
square is `Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange` in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause`. Writing
`S = (π^*ker q) ⊗ 𝒪_{𝐏(ℰ)}(-1)` (`Stacks.ProjectiveBundleConormal.twistedSource`) and `S'` for its
primed counterpart, they are:

1. **`Φ : h^*S ⟶ S'`.** Not constructed. The two factors are available:
   `Stacks.Divisors.quotientKernelBaseChange` identifies the pullback of `ker q`, and
   `Stacks.RelativeProj.symTwistBaseChangeIso` identifies `h^*𝒪_{𝐏(ℰ)}(1)` with
   `𝒪_{𝐏(ℰ')}(1)`. The second is stated at **exactly this substrate**,
   `relativeProj (schemeSheafGradedAlgebra ℰ hqc)`, and is unconditional in `g`, `ℰ` and `ℰ'`;
   the "Not done here" of `ProjectiveBundle/TautologicalDatumBaseChange.lean` concerns the other
   presentation, `Stacks.RelativeProj.projectiveBundle`, and does not bear on anything here.
   What is missing is the passage from `h^*𝒪(1) ≅ 𝒪'(1)` to `h^*𝒪(-1) ≅ 𝒪'(-1)` and the
   assembly of the two factors over the tensor product.
2. **`hΦ`, the base change of the untwisted tautological map.** This is the one genuinely
   mathematical residue. Its inputs are `Stacks.RelativeProj.symTwistBaseChangeIso_spec` — which
   *is* the compatibility of the twist comparison with the two tautological maps, so the
   mathematics is in place — together with the compatibility of the evaluation pairing with the
   base change of an inverse, which is
   `Stacks.ProjBundleInverseBaseChange.inverseQuotientBaseChangeIso_evaluation`. The
   obstacle is that the latter is stated in the *localized* monoidal spelling of
   `Stacks.SheafInternalHom.monoidalCategory`, with
   `Stacks.ProjBundleInverseBaseChange.negOneMulIso'`, whereas everything here is in the
   re-seated `SheafOfModules.monoidalCategorySheafTensor` of
   `Stacks.ProjectiveBundleConormal.monoidalSheafTensor`; `CanonicalMap.lean`'s implementation
   notes record why the re-seated one was chosen and that crossing back costs two comparisons.
3. **`hsrc`, the source coherence.** An equation between two identifications of the source of
   the canonical map; no ideal sheaf and no conormal sheaf occurs in it. It is a *consequence*
   of the data already in the statement rather than a further assumption: `e` and `e'` are each
   pinned uniquely by `hqe` and `hqe'`, because `σ^*(tautologicalMap ℰ)` is an epimorphism and
   the collapse `F ≅ σ^*π^*F` of `Stacks.ProjectiveBundleConormal.pullbackSectionNatIso` is an
   isomorphism, so an equation whose two sides satisfy the same pinning equation is forced.

**Why the reduction stops where it does.** The lift coherence of
`idealSheafLift_baseChange_of_twisted` is proved by the monomorphism
`Stacks.ClosedImmersion.idealSheafι`, which pins a factorization through an ideal sheaf. That
monomorphism is available only *before* `σ'^*` is applied —
`AlgebraicGeometry.Scheme.Modules.pullback` is a left adjoint and does not preserve
monomorphisms — so the clause cannot be proved by pinning the two sides of its own square, and
an identification of the sources has to be produced. That is what `Φ` is, and it is why `Φ`
cannot be eliminated from the reduction.

**No `@[stacks 0B3V]` attribute is attached in this file**: it carries the reduction of the
clause, not the clause. The label is on
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange` in
`StacksFrontier.AlgebraicGeometry.ProjectiveBundleConormal.BaseChangeClause`.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.ProjectiveBundleSplitting
open Stacks.SymGraded

universe u

namespace Stacks.ClosedImmersion

variable {Z Z' W W' : RingedSpace.{u, u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-- **The identification `f^*j^* ≅ i^*k^*` of a commuting square, as a natural isomorphism.**
`Stacks.ClosedImmersion.pullbackCompIso` is its component at a module; naming the natural
isomorphism is what lets a morphism be moved across the square. -/
def pullbackCompNatIso (comm : i ≫ k = f ≫ j) :
    modulePullback j ⋙ modulePullback f ≅ modulePullback k ⋙ modulePullback i :=
  (modulePullbackComp f j).symm ≪≫ modulePullbackCongr comm.symm ≪≫ modulePullbackComp i k

/-- The components of `Stacks.ClosedImmersion.pullbackCompNatIso` are
`Stacks.ClosedImmersion.pullbackCompIso`. -/
theorem pullbackCompNatIso_app (comm : i ≫ k = f ≫ j)
    (M : SheafOfModules.{u} (structureSheafRing W')) :
    (pullbackCompNatIso comm).app M = pullbackCompIso comm M := rfl

/-- **A morphism of modules on `W'` may be moved across the square's identification.** -/
alias pullbackCompIso_naturality := Stacks.ClosedImmersion.pullbackCompIso_hom_naturality

/-- **A morphism compatible with two maps into the structure sheaves lifts to the ideal
sheaves.** Let `i ≫ k = f ≫ j` be a commuting square, let `v : A ⟶ 𝒪_{W'}` be killed by the
structure-sheaf map of `j` and `v' : B ⟶ 𝒪_{Z'}` by that of `i`, so that each factors through
the ideal sheaf, and let `Φ : k^*A ⟶ B` carry `k^*v` to `v'`. Then `Φ` carries the factorization
of `v` to the factorization of `v'`, over `Stacks.ClosedImmersion.idealSheafMap`.

The inclusion of an ideal sheaf is a monomorphism, so the two factorizations may be compared
after composing with it; this is what makes the statement a formality once the compatibility of
the maps into the structure sheaves is known. **It is available only here**, before any further
pullback: `Stacks.ClosedImmersion.modulePullback` is a left adjoint and does not preserve
monomorphisms, so the same comparison read inside `i^*` is not a consequence of anything
below. -/
theorem lift_comp_idealSheafMap (comm : i ≫ k = f ≫ j)
    {A : SheafOfModules.{u} (structureSheafRing W')}
    {B : SheafOfModules.{u} (structureSheafRing Z')}
    (v : A ⟶ SheafOfModules.unit (structureSheafRing W'))
    (hv : v ≫ structureSheafModuleHom j = 0)
    (v' : B ⟶ SheafOfModules.unit (structureSheafRing Z'))
    (hv' : v' ≫ structureSheafModuleHom i = 0)
    (Φ : (modulePullback k).obj A ⟶ B)
    (hΦ : Φ ≫ v' = (modulePullback k).map v ≫ modulePullbackUnitToUnit k) :
    Φ ≫ kernel.lift (structureSheafModuleHom i) v' hv' =
      (modulePullback k).map (kernel.lift (structureSheafModuleHom j) v hv) ≫
        idealSheafMap comm := by
  have hIM : idealSheafMap comm ≫ kernel.ι (structureSheafModuleHom i) =
      (modulePullback k).map (kernel.ι (structureSheafModuleHom j)) ≫
        modulePullbackUnitToUnit k :=
    idealSheafMap_comp_ι comm
  refine (cancel_mono (kernel.ι (structureSheafModuleHom i))).1 ?_
  rw [Category.assoc, kernel.lift_ι, hΦ]
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≫ ·) hIM).symm
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ modulePullbackUnitToUnit k)
    (((modulePullback k).map_comp _ _).symm.trans
      (congrArg (modulePullback k).map (kernel.lift_ι _ _ _))))).symm

end Stacks.ClosedImmersion

namespace Stacks.Conormal

open Stacks.ClosedImmersion

variable {Z Z' W W' : Scheme.{u}} {i : Z ⟶ Z'} {j : W ⟶ W'} {f : Z ⟶ W} {k : Z' ⟶ W'}

/-- **A commuting square of schemes, at the ringed-space spelling** its sheaves of modules are
formed over. -/
theorem comm_toShHom (comm : i ≫ k = f ≫ j) :
    i.toLRSHom.toShHom ≫ k.toLRSHom.toShHom =
      f.toLRSHom.toShHom ≫ j.toLRSHom.toShHom := by
  simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
    congrArg (fun m : Z ⟶ W' => m.toLRSHom.toShHom) comm

variable [IsImmersion i] [IsImmersion j]

/-- **The canonical map of conormal sheaves attached to a commuting square of immersions of
schemes**, `f^*𝒞_j ⟶ 𝒞_i`. The conormal sheaf of an immersion is the pullback along it of its
own ideal sheaf (`Stacks.CartierConormal.conormalSheafIsoPullbackSelf`), and under that
identification the map is `Stacks.ClosedImmersion.conormalSheafMap`: the square's
identification `f^*j^* ≅ i^*k^*` followed by the pullback along `i` of
`Stacks.ClosedImmersion.idealSheafMap`.

The source is ascribed at `AlgebraicGeometry.Scheme.Modules`, which is the spelling
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap` is stated in; everything inside is at the
ringed-space spelling the ideal sheaf is formed over, so the crossing happens once.

This is the canonical map of [Stacks, Tag 01R4] and the right vertical of Tag 0B3V's
base-change square for the conormal isomorphism. -/
@[sga "3 III 4.8.0" "partial"]
def conormalBaseChangeMap (comm : i ≫ k = f ≫ j) :
    (Scheme.Modules.pullback f).obj (Stacks.Conormal.conormalSheaf j) ⟶
      Stacks.Conormal.conormalSheaf i :=
  (modulePullback f.toLRSHom.toShHom).map
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf j).hom ≫
    conormalSheafMap (comm_toShHom comm) ≫
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv

/-- **`Stacks.Conormal.conormalBaseChangeMap` spelled out**: pass to the ideal sheaf of `j`,
cross the square, map the ideal sheaves, and come back. -/
theorem conormalBaseChangeMap_eq (comm : i ≫ k = f ≫ j) :
    conormalBaseChangeMap comm =
      (modulePullback f.toLRSHom.toShHom).map
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf j).hom ≫
        (pullbackCompIso (comm_toShHom comm)
            (Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom)).hom ≫
          (modulePullback i.toLRSHom.toShHom).map (idealSheafMap (comm_toShHom comm)) ≫
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf i).inv :=
  congrArg (fun z => (modulePullback f.toLRSHom.toShHom).map
      (Stacks.CartierConormal.conormalSheafIsoPullbackSelf j).hom ≫ z) (Category.assoc _ _ _)

end Stacks.Conormal

namespace Stacks.ProjectiveBundleConormal

open Stacks.ClosedImmersion

-- `Stacks.ProjectiveBundleConormal.monoidalSheafTensor` is `CanonicalMap.lean`'s monoidal
-- structure on `AlgebraicGeometry.Scheme.Modules` -- the one whose tensor product is the tensor
-- product sheaf of Tag 01CA and whose unit is the structure sheaf, both definitionally. It is a
-- `local instance` there, so it has to be re-enabled here; `AlgebraicGeometry.Scheme.Modules`
-- carries more than one, which is why it is not global.
attribute [local instance] monoidalSheafTensor

/-- **The bookkeeping of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_idealSheafLift`, in a bare
category.** Given a factorization `m = fp ≫ fq ≫ fr`, a retraction `fr ≫ fs = 𝟙`, and the
agreement of `a ≫ b ≫ c` with `fp ≫ fq ≫ t`, the two composites ending in `d` agree.

Stated abstractly on purpose. At the sheaves of modules of a scheme the same manipulation is out
of reach of `rw` and `simp`: `AlgebraicGeometry.Scheme.Modules` and the modules of the
underlying ringed space are definitionally equal but carry syntactically different `Category`
instances, so `CategoryTheory.Functor.map_comp` and `CategoryTheory.Category.assoc` do not match
a composite that mixes them, while unification at default transparency crosses them without
trouble. Hoisting the manipulation here lets the crossing happen once, in `exact`. -/
private theorem comp_eq_of_retraction {D : Type*} [Category D]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Z W : D}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (c : X₂ ⟶ Z) (d : Z ⟶ W)
    (fp : X₀ ⟶ Y₀) (fq : Y₀ ⟶ Y₁) (t : Y₁ ⟶ Z)
    (m : X₀ ⟶ X₃) (fr : Y₁ ⟶ X₃) (fs : X₃ ⟶ Y₁)
    (hm : m = fp ≫ fq ≫ fr) (hrs : fr ≫ fs = 𝟙 Y₁)
    (hres : a ≫ b ≫ c = fp ≫ fq ≫ t) :
    a ≫ b ≫ c ≫ d = m ≫ fs ≫ t ≫ d := by
  rw [hm, reassoc_of% hres]
  simp only [Category.assoc]
  rw [← Category.assoc fr fs, hrs, Category.id_comp]

/-- **The second half of the bookkeeping, in a bare category.** With `x ≫ pn = q ≫ hl` the
passage of the lift across the square, `hl ≫ im = r ≫ l` the lift coherence read after a further
pullback, and `a ≫ b = p ≫ q ≫ r` the source coherence, the two composites agree.

Abstract for the reason recorded on
`Stacks.ProjectiveBundleConormal.comp_eq_of_retraction`. -/
private theorem comp_eq_of_pasting {D : Type*} [Category D]
    {A₀ A₁ A₂ B₀ B₁ Y₀ Y₁ C₀ : D}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (l : A₂ ⟶ C₀)
    (p : A₀ ⟶ B₀) (q : B₀ ⟶ B₁) (r : B₁ ⟶ A₂)
    (x : B₀ ⟶ Y₀) (pn : Y₀ ⟶ Y₁) (im : Y₁ ⟶ C₀) (hl : B₁ ⟶ Y₁)
    (hnat : x ≫ pn = q ≫ hl) (hlift : hl ≫ im = r ≫ l)
    (hsrc : a ≫ b = p ≫ q ≫ r) :
    a ≫ b ≫ l = p ≫ x ≫ pn ≫ im := by
  rw [← Category.assoc a b l, hsrc, ← Category.assoc x pn im, hnat, Category.assoc,
    Category.assoc, Category.assoc, hlift]

variable {X X' : Scheme.{u}} (g : X' ⟶ X)
  (E : X.Modules) [E.IsQuasicoherent] (E' : X'.Modules) [E'.IsQuasicoherent]
  (hE : E' ≅ (Scheme.Modules.pullback g).obj E)
  (Q : Stacks.Divisors.InvertibleQuotient X E) (Q' : Stacks.Divisors.InvertibleQuotient X' E')
  (hL : Q'.L ≅ (Scheme.Modules.pullback g).obj Q.L)
  (hq : Q'.q ≫ hL.hom = hE.hom ≫ (Scheme.Modules.pullback g).map Q.q)
  {σ : X ⟶ (bundle E).scheme} (hσ : σ ≫ (bundle E).toBase = 𝟙 X)
  (e : (Scheme.Modules.pullback σ).obj (tautologicalTwist E (symPieces E)) ≅ Q.L)
  (hqe : (Scheme.Modules.pullbackId X).inv.app E ≫
    (Scheme.Modules.pullbackCongr hσ).inv.app E ≫
      (Scheme.Modules.pullbackComp σ (bundle E).toBase).inv.app E ≫
        (Scheme.Modules.pullback σ).map (tautologicalMap E (symPieces E)) ≫ e.hom = Q.q)
  {σ' : X' ⟶ (bundle E').scheme} (hσ' : σ' ≫ (bundle E').toBase = 𝟙 X')
  (e' : (Scheme.Modules.pullback σ').obj (tautologicalTwist E' (symPieces E')) ≅ Q'.L)
  (hqe' : (Scheme.Modules.pullbackId X').inv.app E' ≫
    (Scheme.Modules.pullbackCongr hσ').inv.app E' ≫
      (Scheme.Modules.pullbackComp σ' (bundle E').toBase).inv.app E' ≫
        (Scheme.Modules.pullback σ').map (tautologicalMap E' (symPieces E')) ≫ e'.hom = Q'.q)
  [IsImmersion σ] [IsImmersion σ']

/-- **The base-change comparison morphism of the two bundles** at the presentation
`Stacks.ProjectiveBundleConormal.bundle` that the canonical conormal map is built over. -/
abbrev bundleBaseChangeHom : (bundle E').scheme ⟶ (bundle E).scheme :=
  Stacks.ProjectiveBundle.baseChangeHom g E (symPieces E) E' (symPieces E') hE

/-- **The source of the untwisted tautological map**, `(π^*ker q) ⊗ 𝒪_{𝐏(ℰ)}(-1)`. Named
because the monoidal structure of `Stacks.ProjectiveBundleConormal.monoidalSheafTensor` is
stated at `AlgebraicGeometry.Scheme.Modules`, and the tensor product resolves only against that
expected type: written inline, the two factors unify at the modules of the underlying sheafed
space instead and no `MonoidalCategoryStruct` is found. -/
abbrev twistedSource : (bundle E).scheme.Modules :=
  (Scheme.Modules.pullback (bundle E).toBase).obj (kernel Q.q) ⊗ inverseTautologicalTwist E

omit [IsImmersion σ] [IsImmersion σ'] in
include hqe hqe' in
/-- **The lift coherence of Tag 0B3V's base-change clause, discharged.** An identification `Φ`
of `h^*((π^*ker q) ⊗ 𝒪(-1))` with its primed counterpart that carries the base change of the
untwisted tautological map `ṽ` to `ṽ'` carries the base change of
`Stacks.ProjectiveBundleConormal.idealSheafLift` to the primed lift, over
`Stacks.ClosedImmersion.idealSheafMap`.

`Φ` is a variable: nothing here constructs it, and nothing here needs it to be invertible. This
is `Stacks.ClosedImmersion.lift_comp_idealSheafMap` at the two untwisted tautological maps, whose
vanishing against the structure-sheaf maps is
`Stacks.ProjectiveBundleConormal.kernelTautologicalMapTwisted_comp_structureSheafUnit`. -/
theorem idealSheafLift_baseChange_of_twisted
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (Φ : (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).obj
          (twistedSource E Q) ⟶ twistedSource E' Q')
    (hΦ : Φ ≫ kernelTautologicalMapTwisted E' Q' =
      (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).map
          (kernelTautologicalMapTwisted E Q) ≫
        modulePullbackUnitToUnit (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom) :
    Φ ≫ (idealSheafLift E' Q' hσ' e' hqe' :
        _ ⟶ Stacks.ClosedImmersion.idealSheaf σ'.toLRSHom.toShHom) =
      (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).map
          (idealSheafLift E Q hσ e hqe :
            _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom) ≫
        idealSheafMap (Stacks.Conormal.comm_toShHom comm) :=
  lift_comp_idealSheafMap (Stacks.Conormal.comm_toShHom comm) _
    (kernelTautologicalMapTwisted_comp_structureSheafUnit E Q hσ e hqe) _
    (kernelTautologicalMapTwisted_comp_structureSheafUnit E' Q' hσ' e' hqe') Φ hΦ

omit [IsImmersion σ] [IsImmersion σ'] in
include hqe hqe' in
/-- **Tag 0B3V's base-change clause for the conormal isomorphism, reduced to the source
comparison and the untwisted tautological map.**

Given an identification `Φ` of `h^*((π^*ker q) ⊗ 𝒪(-1))` with its primed counterpart that
carries the base change of the untwisted tautological map to the primed one (`hΦ`), and the
agreement of `Stacks.Divisors.conormalSourceBaseChange` with `σ'^*Φ` across the square
(`hsrc`), the hypothesis of
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap_baseChange_of_idealSheafLift` holds.

The passage of the lift across the square is
`Stacks.ClosedImmersion.pullbackCompIso_naturality`; the lift coherence is
`Stacks.ProjectiveBundleConormal.idealSheafLift_baseChange_of_twisted`; everything else is
associativity. Note that `hsrc` mentions no ideal sheaf and no conormal sheaf: it is an equation
between two identifications of the *source* of the canonical map. -/
theorem idealSheafLift_baseChange_of_source
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (Φ : (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).obj
          (twistedSource E Q) ⟶ twistedSource E' Q')
    (hΦ : Φ ≫ kernelTautologicalMapTwisted E' Q' =
      (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).map
          (kernelTautologicalMapTwisted E Q) ≫
        modulePullbackUnitToUnit (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom)
    (hsrc : (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (pullbackCompIso (Stacks.Conormal.comm_toShHom comm) (twistedSource E Q)).hom ≫
          (modulePullback σ'.toLRSHom.toShHom).map Φ) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv ≫
          (modulePullback σ'.toLRSHom.toShHom).map
            (idealSheafLift E' Q' hσ' e' hqe' :
              _ ⟶ Stacks.ClosedImmersion.idealSheaf σ'.toLRSHom.toShHom) =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (modulePullback g.toLRSHom.toShHom).map
            ((modulePullback σ.toLRSHom.toShHom).map
              (idealSheafLift E Q hσ e hqe :
                _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom)) ≫
          conormalSheafMap (Stacks.Conormal.comm_toShHom comm) := by
  have hnat := pullbackCompIso_naturality (Stacks.Conormal.comm_toShHom comm)
    (idealSheafLift E Q hσ e hqe : _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom)
  have hlift : (modulePullback σ'.toLRSHom.toShHom).map
        ((modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).map
          (idealSheafLift E Q hσ e hqe :
            _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom)) ≫
      (modulePullback σ'.toLRSHom.toShHom).map
        (idealSheafMap (Stacks.Conormal.comm_toShHom comm)) =
      (modulePullback σ'.toLRSHom.toShHom).map Φ ≫
        (modulePullback σ'.toLRSHom.toShHom).map
          (idealSheafLift E' Q' hσ' e' hqe' :
            _ ⟶ Stacks.ClosedImmersion.idealSheaf σ'.toLRSHom.toShHom) :=
    (((modulePullback σ'.toLRSHom.toShHom).map_comp _ _).symm.trans
      (congrArg (modulePullback σ'.toLRSHom.toShHom).map
        (idealSheafLift_baseChange_of_twisted g E E' hE Q Q' hσ e hqe hσ' e' hqe'
          comm Φ hΦ).symm)).trans
      ((modulePullback σ'.toLRSHom.toShHom).map_comp _ _)
  exact comp_eq_of_pasting _ _ _ _ _ _ _ _ _ _ hnat hlift hsrc

include hqe hqe' in
/-- **Tag 0B3V's base-change square for the conormal isomorphism, reduced to the base change of
the ideal-sheaf lift.**

The square whose horizontals are `Stacks.ProjectiveBundleConormal.conormalCanonicalMap` at the
two bundles, whose left vertical is `Stacks.Divisors.conormalSourceBaseChange` and whose right
vertical is `Stacks.Conormal.conormalBaseChangeMap`, commutes as soon as the hypothesis `hres`
does. Everything the canonical map adds to the ideal-sheaf lift it is built from — the two
identifications `𝒞 ≅ σ^*ℐ(σ)` of `Stacks.CartierConormal.conormalSheafIsoPullbackSelf` and the
functoriality of `g^*` — is discharged here.

`hres` is not proved here, and it is the whole remainder of the clause; see this module's
"What is still owed, precisely". -/
theorem conormalCanonicalMap_baseChange_of_idealSheafLift
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (hres : (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv ≫
          (modulePullback σ'.toLRSHom.toShHom).map
            (idealSheafLift E' Q' hσ' e' hqe' :
              _ ⟶ Stacks.ClosedImmersion.idealSheaf σ'.toLRSHom.toShHom) =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (modulePullback g.toLRSHom.toShHom).map
            ((modulePullback σ.toLRSHom.toShHom).map
              (idealSheafLift E Q hσ e hqe :
                _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom)) ≫
          conormalSheafMap (Stacks.Conormal.comm_toShHom comm)) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        conormalCanonicalMap E' Q' hσ' e' hqe' =
      (Scheme.Modules.pullback g).map (conormalCanonicalMap E Q hσ e hqe) ≫
        Stacks.Conormal.conormalBaseChangeMap comm := by
  have hcancel : (modulePullback g.toLRSHom.toShHom).map
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv ≫
      (modulePullback g.toLRSHom.toShHom).map
        (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom = 𝟙 _ :=
    ((modulePullback g.toLRSHom.toShHom).map_comp _ _).symm.trans
      ((congrArg (modulePullback g.toLRSHom.toShHom).map
        (Iso.inv_hom_id (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ))).trans
          ((modulePullback g.toLRSHom.toShHom).map_id _))
  change (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
      ((pullbackSourceIso E' Q' hσ' e').inv ≫
        (modulePullback σ'.toLRSHom.toShHom).map
            (idealSheafLift E' Q' hσ' e' hqe' :
              _ ⟶ Stacks.ClosedImmersion.idealSheaf σ'.toLRSHom.toShHom) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ').inv) =
    (modulePullback g.toLRSHom.toShHom).map
        ((pullbackSourceIso E Q hσ e).inv ≫
          (modulePullback σ.toLRSHom.toShHom).map
              (idealSheafLift E Q hσ e hqe :
                _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom) ≫
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv) ≫
      ((modulePullback g.toLRSHom.toShHom).map
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).hom ≫
        conormalSheafMap (Stacks.Conormal.comm_toShHom comm) ≫
          (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ').inv)
  have hm : (modulePullback g.toLRSHom.toShHom).map
        ((pullbackSourceIso E Q hσ e).inv ≫
          (modulePullback σ.toLRSHom.toShHom).map
              (idealSheafLift E Q hσ e hqe :
                _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom) ≫
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv) =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (modulePullback g.toLRSHom.toShHom).map
            ((modulePullback σ.toLRSHom.toShHom).map
              (idealSheafLift E Q hσ e hqe :
                _ ⟶ Stacks.ClosedImmersion.idealSheaf σ.toLRSHom.toShHom)) ≫
          (modulePullback g.toLRSHom.toShHom).map
            (Stacks.CartierConormal.conormalSheafIsoPullbackSelf σ).inv :=
    ((modulePullback g.toLRSHom.toShHom).map_comp _ _).trans
      (congrArg ((modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫ ·)
        ((modulePullback g.toLRSHom.toShHom).map_comp _ _))
  exact comp_eq_of_retraction _ _ _ _ _ _ _ _ _ _ hm hcancel hres

include hqe hqe' in
/-- **Tag 0B3V's base-change clause for the conormal isomorphism, from the source comparison and
the untwisted tautological map.** The square whose horizontals are
`Stacks.ProjectiveBundleConormal.conormalCanonicalMap` at the two bundles, whose left vertical
is `Stacks.Divisors.conormalSourceBaseChange` and whose right vertical is
`Stacks.Conormal.conormalBaseChangeMap`, commutes as soon as there is an identification `Φ` of
`h^*((π^*ker q) ⊗ 𝒪(-1))` with its primed counterpart which

* carries the base change of the untwisted tautological map to the primed one (`hΦ`), and
* agrees, after `σ'^*` and across the square, with
  `Stacks.Divisors.conormalSourceBaseChange` (`hsrc`).

This is `conormalCanonicalMap_baseChange_of_idealSheafLift` fed by
`idealSheafLift_baseChange_of_source`. It is the sharpest form of the clause this file reaches:
no ideal sheaf and no conormal sheaf occurs in either hypothesis, and neither hypothesis is
proved here. See this module's "What is still owed, precisely". -/
theorem conormalCanonicalMap_baseChange_of_source
    (comm : σ' ≫ bundleBaseChangeHom g E E' hE = g ≫ σ)
    (Φ : (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).obj
          (twistedSource E Q) ⟶ twistedSource E' Q')
    (hΦ : Φ ≫ kernelTautologicalMapTwisted E' Q' =
      (modulePullback (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom).map
          (kernelTautologicalMapTwisted E Q) ≫
        modulePullbackUnitToUnit (bundleBaseChangeHom g E E' hE).toLRSHom.toShHom)
    (hsrc : (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        (pullbackSourceIso E' Q' hσ' e').inv =
      (modulePullback g.toLRSHom.toShHom).map (pullbackSourceIso E Q hσ e).inv ≫
        (pullbackCompIso (Stacks.Conormal.comm_toShHom comm) (twistedSource E Q)).hom ≫
          (modulePullback σ'.toLRSHom.toShHom).map Φ) :
    (Stacks.Divisors.conormalSourceBaseChange g E E' hE Q Q' hL hq).hom ≫
        conormalCanonicalMap E' Q' hσ' e' hqe' =
      (Scheme.Modules.pullback g).map (conormalCanonicalMap E Q hσ e hqe) ≫
        Stacks.Conormal.conormalBaseChangeMap comm :=
  conormalCanonicalMap_baseChange_of_idealSheafLift g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe'
    comm
    (idealSheafLift_baseChange_of_source g E E' hE Q Q' hL hq hσ e hqe hσ' e' hqe' comm Φ hΦ hsrc)

end Stacks.ProjectiveBundleConormal

end
