module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernComposition
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.InternalHomLocalKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Composition
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.ConormalSequence
public import StacksCore.Tactic.StacksAttribute

/-!
# Gysin maps of a composite of regular immersions

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `i : Z ⟶ Y` and
`j : Y ⟶ X` be regular immersions of schemes locally of finite type over `S`. Stacks 0FF0 asserts
two things: that `j ∘ i` is again a regular immersion, and that

  `(j ∘ i)^! = i^! ∘ j^!`.

The first assertion is Stacks 067Q. The second follows from Stacks 0FEC once the three canonical
normal bundles of `i`, `j` and `j ∘ i` are exhibited as a conormal-compatible triple, and that is
what this file constructs: the normal bundle of a regular immersion is the dual of its conormal
sheaf, the conormal sheaf of a regular immersion is finite locally free and therefore reflexive,
and the short exact sequence

  `0 ⟶ i^* 𝒞_{Y/X} ⟶ 𝒞_{Z/X} ⟶ 𝒞_{Z/Y} ⟶ 0`

of Stacks 063N is the sequence of duals that Stacks 0FEC asks for, read through reflexivity.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion` — the normal bundle of a regular
  immersion of locally Noetherian schemes, as a virtual normal bundle in the sense of
  Stacks 0FBQ.
* `Stacks.Chow.ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion` — the three normal
  bundles of a pair of regular immersions, together with the short exact sequence of their duals
  and its two squares against the conormal sequence of Stacks 062S.

## Main results

* `Stacks.AlgebraicGeometry.isRegularImmersion_comp` — the first assertion of Stacks 0FF0; it is
  Stacks 067Q and is proved in
  `StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.Composition`, so this file only
  records the tag against it.
* `Stacks.Chow.isIso_toDoubleDual_conormalModule` — the conormal sheaf of a regular
  immersion of locally Noetherian schemes is reflexive.
* `Stacks.Chow.localizedChernClass_cap_eq_bivariantCompositeCap_of_isRegularImmersion` — the
  second assertion of Stacks 0FF0 read on cap products: the Gysin map of `j ∘ i` is cap with
  `j^!` followed by cap with `i^!`.
* `Stacks.Chow.localizedChernClass_eq_bivariantComposite_of_isRegularImmersion` — the second
  assertion of Stacks 0FF0 as an equality of bivariant classes: the Gysin class of `j ∘ i` is the
  composite of Stacks 0B75 of the Gysin classes of `i` and of `j`.

## Implementation notes

### The normal bundle through reflexivity

`Stacks.Chow.VirtualNormalBundle` asks for a finite locally free module `𝒩` together with a
surjection `𝒩^∨ ⟶ 𝒞`. For a regular immersion the conormal sheaf `𝒞` is itself finite locally
free, by Stacks 063N, and `𝒩 = 𝒞^∨` works: `𝒩^∨ = 𝒞^∨∨` is `𝒞` again, through the canonical map
`Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual`, which is an isomorphism for a finite
locally free module on a locally Noetherian scheme. Local Noetherianness of the source enters
only here; in the situation of Stacks 0FF0 it holds because the source is locally of finite type
over the locally Noetherian base.

So the three structural surjections of the triple below are isomorphisms, and the sequence of
duals it carries is the conormal sequence conjugated by them. Short exactness is therefore
exactly the short exactness of the conormal sequence, which for a regular immersion `i` is
Stacks 063N.

`Stacks.Chow.isFiniteLocallyFree_dualSheaf_of_schemeOpens` repeats, for the site of opens of a
scheme, the statement of Stacks 0FA7 that the dual of a finite locally free module is finite
locally free: every point has a neighbourhood trivialising the module on a finite index set, and
the dual of the restriction is the restriction of the dual.

### What the second assertion rests on

The localized Chern class `c(Z ⟶ X, 𝒩)` of Stacks 0FBK is not constructed in this repository and
is a parameter, `Stacks.Chow.LocalizedChernClassRule`; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.LocalizedChernComposition`. The two results
below consume the two theorems of Stacks 0FEC in the repository's own form, in which the
composition formula for the three parameterized classes is an input. What this file supplies is
the geometric half of Stacks 0FF0: the datum that instantiates Stacks 0FEC at a pair of regular
immersions.

## References

* [Stacks Project, Tag 0FF0](https://stacks.math.columbia.edu/tag/0FF0)
* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 067Q](https://stacks.math.columbia.edu/tag/067Q)
* [Stacks Project, Tag 063N](https://stacks.math.columbia.edu/tag/063N)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.SheafOfModules.InternalHom
open Stacks.Immersion Stacks.Thickenings

universe u

namespace Stacks.Chow

/-! ### The dual of a finite locally free module on a scheme -/

/-- The dual `ℰ^∨ = SheafHom(ℰ, 𝒪_X)` of a finite locally free module on a scheme is finite
locally free; the rank of `ℰ` is not assumed constant. Every point has a neighbourhood on which a
local free presentation trivialises `ℰ` on a finite index set, and there `ℰ^∨` is free on the
same index set. -/
theorem isFiniteLocallyFree_dualSheaf_of_schemeOpens {X : Scheme.{u}} (E : X.Modules)
    (hE : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) E) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := X.ringCatSheaf) (dualSheaf E) := by
  apply _root_.AlgebraicGeometry.SheafOfModules.isFiniteLocallyFree_of_forall_exists_iso_free_over
  intro x
  obtain ⟨q, hq, hqf⟩ := hE.exists_isFiniteLocallyFreeData
  obtain ⟨idx, hxi⟩ := ((Opens.coversTop_iff _ q.X).1 q.coversTop).exists_mem x
  have hiso : IsIso (q.generators idx).π := hq.isIso idx
  have hfin : Finite (q.generators idx).I := (hqf.isFiniteType idx).finite
  exact ⟨q.X idx, hxi, (q.generators idx).I, hfin,
    ⟨Stacks.AlgebraicGeometry.ReflexiveModules.freeIsoDualSheafOver X (q.X idx) E
      (asIso (q.generators idx).π)⟩⟩

/-! ### The first assertion

It is Stacks 067Q, proved as `Stacks.AlgebraicGeometry.isRegularImmersion_comp`: the composite of
two regular immersions is a regular immersion, with local finite type over the base playing no
role. -/

add_to_stacks 0FF0 "first assertion: the composite of two regular immersions of schemes locally \
of finite type over the base is a regular immersion; local finite type over the base is not \
used, and the assertion is Stacks 067Q" Stacks.AlgebraicGeometry.isRegularImmersion_comp

/-! ### Reflexivity of the conormal sheaf of a regular immersion -/

/-- The conormal sheaf `𝒞_{Z/X}` of an immersion, read as a module on the source. -/
abbrev conormalModule {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] : Z.Modules :=
  immersionConormalSheaf i

/-- The conormal sheaf of a regular immersion is finite locally free, by Stacks 063N. -/
theorem isFiniteLocallyFree_conormalModule {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (hi : IsRegularImmersion i) :
    _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := Z.ringCatSheaf) (conormalModule i) :=
  isFiniteLocallyFree_conormalSheaf_of_isH1RegularImmersion i
    (isH1RegularImmersion_of_isKoszulRegularImmersion i
      (isKoszulRegularImmersion_of_isRegularImmersion i hi))

/-- **The conormal sheaf of a regular immersion of locally Noetherian schemes is reflexive.** It
is finite locally free by Stacks 063N, hence coherent by Stacks 01XZ, and a coherent finite
locally free module on a locally Noetherian scheme is reflexive. -/
theorem isIso_toDoubleDual_conormalModule {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) :
    IsIso (toDoubleDual (conormalModule i)) := by
  have hflf := isFiniteLocallyFree_conormalModule i hi
  have hcoh : (conormalModule i).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isFiniteLocallyFree Z
      (conormalModule i)
  exact Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree
    (conormalModule i) ((Scheme.Modules.isFiniteLocallyFree_iff (conormalModule i)).2 hflf)

/-- The reflexivity isomorphism `𝒞_{Z/X} ≅ 𝒞_{Z/X}^∨∨` of the conormal sheaf of a regular
immersion of locally Noetherian schemes. -/
def conormalReflexiveIso {Z X : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsImmersion i]
    (hi : IsRegularImmersion i) : conormalModule i ≅ dualSheaf (dualSheaf (conormalModule i)) :=
  @asIso _ _ _ _ (toDoubleDual (conormalModule i)) (isIso_toDoubleDual_conormalModule i hi)

/-- The forward map of `conormalReflexiveIso` is the canonical map to the double dual. -/
@[simp]
theorem conormalReflexiveIso_hom {Z X : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsImmersion i] (hi : IsRegularImmersion i) :
    (conormalReflexiveIso i hi).hom = toDoubleDual (conormalModule i) :=
  rfl

/-- The structural surjection `𝒩^∨ ⟶ 𝒞_{Z/X}` of the normal bundle of a regular immersion: the
inverse of the reflexivity isomorphism of the conormal sheaf. -/
def regularNormalSurjection {Z X : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsImmersion i] (hi : IsRegularImmersion i) :
    dualSheaf (dualSheaf (conormalModule i)) ⟶ conormalModule i :=
  (conormalReflexiveIso i hi).inv

/-- The map `regularNormalSurjection` is an epimorphism. -/
theorem epi_regularNormalSurjection {Z X : Scheme.{u}} [IsLocallyNoetherian Z] (i : Z ⟶ X)
    [IsImmersion i] (hi : IsRegularImmersion i) : Epi (regularNormalSurjection i hi) :=
  inferInstanceAs (Epi (conormalReflexiveIso i hi).inv)

/-- The canonical map to the double dual followed by `regularNormalSurjection` is the identity. -/
@[simp]
theorem toDoubleDual_comp_regularNormalSurjection {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) :
    toDoubleDual (conormalModule i) ≫ regularNormalSurjection i hi = 𝟙 _ :=
  (conormalReflexiveIso i hi).hom_inv_id

/-- `regularNormalSurjection` followed by the canonical map to the double dual is the identity. -/
@[simp]
theorem regularNormalSurjection_comp_toDoubleDual {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) :
    regularNormalSurjection i hi ≫ toDoubleDual (conormalModule i) = 𝟙 _ :=
  (conormalReflexiveIso i hi).inv_hom_id

/-! ### The normal bundle of a regular immersion -/

/-- **The normal bundle of a regular immersion.** For a regular immersion `i : Z ⟶ X` of locally
Noetherian schemes the conormal sheaf `𝒞_{Z/X}` is finite locally free, and its dual is a virtual
normal bundle for `i` in the sense of Stacks 0FBQ: the dual of the dual is `𝒞_{Z/X}` again, so
the structural surjection may be taken to be an isomorphism. -/
def VirtualNormalBundle.ofIsRegularImmersion {Z X : Scheme.{u}} [IsLocallyNoetherian Z]
    (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) : VirtualNormalBundle i where
  bundle := dualSheaf (conormalModule i)
  isFiniteLocallyFree :=
    isFiniteLocallyFree_dualSheaf_of_schemeOpens (conormalModule i)
      (isFiniteLocallyFree_conormalModule i hi)
  surjection := regularNormalSurjection i hi
  epi := epi_regularNormalSurjection i hi

/-- The bundle of `VirtualNormalBundle.ofIsRegularImmersion` is the dual `𝒞_{Z/X}^∨` of the
conormal sheaf. -/
@[simp]
theorem VirtualNormalBundle.ofIsRegularImmersion_bundle {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) :
    (VirtualNormalBundle.ofIsRegularImmersion i hi).bundle = dualSheaf (conormalModule i) :=
  rfl

/-- The structural surjection of `VirtualNormalBundle.ofIsRegularImmersion` is
`regularNormalSurjection`. -/
@[simp]
theorem VirtualNormalBundle.ofIsRegularImmersion_surjection {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] (i : Z ⟶ X) [IsImmersion i] (hi : IsRegularImmersion i) :
    (VirtualNormalBundle.ofIsRegularImmersion i hi).surjection = regularNormalSurjection i hi :=
  rfl

/-! ### Conjugating a short exact sequence by isomorphisms of its terms -/

section Conjugation

variable {C : Type*} [Category C]

/-- Conjugating a morphism by isomorphisms of its source and target and then undoing the
isomorphism of the target. -/
theorem conjugate_comp_inv {A A' B B' : C} (α : A ≅ A') (β : B ≅ B') (a : A ⟶ B) :
    (α.inv ≫ a ≫ β.hom) ≫ β.inv = α.inv ≫ a := by
  rw [Category.assoc, Category.assoc, β.hom_inv_id, Category.comp_id]

variable [Limits.HasZeroMorphisms C]

/-- A short complex conjugated by isomorphisms of its three terms is again a complex. -/
theorem conjugate_comp_conjugate_eq_zero (S : ShortComplex C) {A' B' D' : C} (α : S.X₁ ≅ A')
    (β : S.X₂ ≅ B') (γ : S.X₃ ≅ D') :
    (α.inv ≫ S.f ≫ β.hom) ≫ β.inv ≫ S.g ≫ γ.hom = 0 := by
  rw [← Category.assoc, conjugate_comp_inv α β S.f, Category.assoc, S.zero_assoc,
    Limits.zero_comp, Limits.comp_zero]

/-- A short exact sequence conjugated by isomorphisms of its three terms is short exact. -/
theorem shortExact_conjugate (S : ShortComplex C) (hse : S.ShortExact) {A' B' D' : C}
    (α : S.X₁ ≅ A') (β : S.X₂ ≅ B') (γ : S.X₃ ≅ D') :
    (ShortComplex.mk (α.inv ≫ S.f ≫ β.hom) (β.inv ≫ S.g ≫ γ.hom)
      (conjugate_comp_conjugate_eq_zero S α β γ)).ShortExact :=
  ShortComplex.shortExact_of_iso
    (ShortComplex.isoMk α β γ (by simp) (by simp)) hse

end Conjugation

/-- A short exact sequence of modules on a scheme, conjugated by isomorphisms of its three
terms, is a short exact sequence in the sense of Stacks 0FEC. -/
theorem isShortExactSequenceOfModules_conjugate {W : Scheme.{u}}
    (S : ShortComplex (SheafOfModules.{u} W.ringCatSheaf)) (hse : S.ShortExact)
    {A' B' D' : SheafOfModules.{u} W.ringCatSheaf} (α : S.X₁ ≅ A') (β : S.X₂ ≅ B')
    (γ : S.X₃ ≅ D') :
    IsShortExactSequenceOfModules (α.inv ≫ S.f ≫ β.hom) (β.inv ≫ S.g ≫ γ.hom) :=
  ⟨conjugate_comp_conjugate_eq_zero S α β γ, shortExact_conjugate S hse α β γ⟩

/-! ### The conormal-compatible triple of a pair of regular immersions -/

section Triple

variable {Z Y X : Scheme.{u}} [IsLocallyNoetherian Z] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
  (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] (hi : IsRegularImmersion i)
  (hj : IsRegularImmersion j)

/-- **Stacks 0FF0, the geometric input of the second assertion.** The three normal bundles of a
pair of regular immersions `Z ⟶ Y ⟶ X` of locally Noetherian schemes form a conormal-compatible
triple in the sense of Stacks 0FEC: the sequence of their duals is the conormal sequence of
Stacks 062S conjugated by the three reflexivity isomorphisms, it is short exact by Stacks 063N,
and its two squares against the conormal sequence commute because the three structural
surjections are the inverses of those isomorphisms. -/
@[stacks 0FF0 "second assertion: the three normal bundles of a pair of regular immersions \
satisfy the hypothesis of Stacks 0FEC, by the short exact conormal sequence of Stacks 063N"]
def ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion :
    ConormalCompatibleVirtualNormalBundles i j where
  bundleZX := VirtualNormalBundle.ofIsRegularImmersion (i ≫ j)
    (Stacks.AlgebraicGeometry.isRegularImmersion_comp i j hi hj)
  bundleZY := VirtualNormalBundle.ofIsRegularImmersion i hi
  bundleYX := VirtualNormalBundle.ofIsRegularImmersion j hj
  dualLeft := ((modulePullback i.toLRSHom.toShHom).mapIso (conormalReflexiveIso j hj)).inv ≫
    conormalLeftMap i j ≫
      (conormalReflexiveIso (i ≫ j)
        (Stacks.AlgebraicGeometry.isRegularImmersion_comp i j hi hj)).hom
  dualRight := (conormalReflexiveIso (i ≫ j)
      (Stacks.AlgebraicGeometry.isRegularImmersion_comp i j hi hj)).inv ≫
    conormalSequenceRightMap i j ≫ (conormalReflexiveIso i hi).hom
  shortExact :=
    isShortExactSequenceOfModules_conjugate (conormalSequenceShortComplex i j)
      (conormalSequence_shortExact i j
        (isH1RegularImmersion_of_isKoszulRegularImmersion i
          (isKoszulRegularImmersion_of_isRegularImmersion i hi)))
      ((modulePullback i.toLRSHom.toShHom).mapIso (conormalReflexiveIso j hj))
      (conormalReflexiveIso (i ≫ j) (Stacks.AlgebraicGeometry.isRegularImmersion_comp i j hi hj))
      (conormalReflexiveIso i hi)
  leftSquare :=
    conjugate_comp_inv ((modulePullback i.toLRSHom.toShHom).mapIso (conormalReflexiveIso j hj))
      (conormalReflexiveIso (i ≫ j)
        (Stacks.AlgebraicGeometry.isRegularImmersion_comp i j hi hj))
      (conormalLeftMap i j)
  rightSquare :=
    conjugate_comp_inv
      (conormalReflexiveIso (i ≫ j)
        (Stacks.AlgebraicGeometry.isRegularImmersion_comp i j hi hj))
      (conormalReflexiveIso i hi) (conormalSequenceRightMap i j)

end Triple

/-! ### The second assertion -/

section Composition

variable (C : ChowSituation.{u}) (G : GysinSystem C) {Z Y X : Scheme.{u}} (sZ : Z ⟶ C.S)
  [LocallyOfFiniteType sZ] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] [IsLocallyNoetherian Z] [IsLocallyNoetherian Y] (i : Z ⟶ Y)
  [IsImmersion i] [LocallyOfFiniteType i] (j : Y ⟶ X) [IsImmersion j] [LocallyOfFiniteType j]
  (hsi : i ≫ sY = sZ) (hsj : j ≫ sX = sY) (hpp : ProperPushforwardDescends C) (p q : ℤ)
  (cloc : LocalizedChernClassRule C G) (hi : IsRegularImmersion i) (hj : IsRegularImmersion j)

/-- **Stacks 0FF0, second assertion, read on cap products.** For regular immersions
`i : Z ⟶ Y` and `j : Y ⟶ X` of schemes locally of finite type over the base, equipped with their
canonical normal bundles, the Gysin map of `j ∘ i` on a test scheme `t : T ⟶ X` is: cap with
`j^!`, then cap with `i^!`, then push forward along the associativity isomorphism
`(T ×_X Y) ×_Y Z ≅ T ×_X Z` of pullbacks.

This is Stacks 0FEC at the conormal-compatible triple of the two regular immersions, so the
composition formula for the three parameterized classes of Stacks 0FBK is an input, as it is in
the two theorems of Stacks 0FEC themselves. -/
@[stacks 0FF0 "second assertion, (j ∘ i)^! = i^! ∘ j^! read on cap products, at the canonical \
normal bundles of the two regular immersions; the localized Chern class of Stacks 0FBK is a \
parameter and the composition formula of Stacks 0FEC is an input, exactly as in Stacks 0FEC"]
theorem localizedChernClass_cap_eq_bivariantCompositeCap_of_isRegularImmersion
    (hc : IsBivariantClassComposition C G sZ sY sX i j hsi hsj hpp p q
      (cloc sZ sY i hsi
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZY p)
      (cloc sY sX j hsj
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleYX q)
      (cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hsi hsj)
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZX (p + q)))
    {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k) :
    chowGroupDegreeEquiv C (pullback.fst (i ≫ j) t ≫ sZ)
        (by ring : k - (p + q) = (k - q) - p)
        ((cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hsi hsj)
          (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZX
          (p + q)).cap t k α) =
      bivariantCompositeCap C G sZ sY sX i j hsi hsj hpp p q
        (cloc sZ sY i hsi
          (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZY p)
        (cloc sY sX j hsj
          (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleYX q)
        t k α :=
  localizedChernClass_cap_eq_bivariantCompositeCap C G sZ sY sX i j hsi hsj hpp p q cloc
    (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj) hc t k α

/-- **Stacks 0FF0, second assertion, as an equality of bivariant classes.** For regular
immersions `i : Z ⟶ Y` and `j : Y ⟶ X` of schemes locally of finite type over the base, equipped
with their canonical normal bundles, the Gysin class of `j ∘ i` is the composite of Stacks 0B75
of the Gysin class of `i` with the Gysin class of `j`:

  `(j ∘ i)^! = i^! ∘ j^!`   in `A^{p+q}(Z ⟶ X)`.

Both classes satisfy the composition formula of Stacks 0FEC — the composite by Stacks 0FE0 — and
that formula determines the class, so they agree. -/
@[stacks 0FF0 "second assertion, (j ∘ i)^! = i^! ∘ j^! as an equality of bivariant classes, at \
the canonical normal bundles of the two regular immersions; the localized Chern class of \
Stacks 0FBK is a parameter and the composition formula of Stacks 0FEC is an input, exactly as \
in Stacks 0FEC"]
theorem localizedChernClass_eq_bivariantComposite_of_isRegularImmersion
    (hgys : G.IsNaturalUnderBaseChangeIso)
    (hgysc : G.IsNaturalUnderPullbackCompPushforward)
    (hc : IsBivariantClassComposition C G sZ sY sX i j hsi hsj hpp p q
      (cloc sZ sY i hsi
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZY p)
      (cloc sY sX j hsj
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleYX q)
      (cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hsi hsj)
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZX
        (p + q))) :
    cloc sZ sX (i ≫ j) (comp_comp_structureMorphism_eq hsi hsj)
        (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZX
        (p + q) =
      bivariantComposite C G sZ sY sX i j hsi hsj p q
        (cloc sZ sY i hsi
          (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleZY p)
        (cloc sY sX j hsj
          (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj).bundleYX q)
        hgys hgysc :=
  eq_localizedChernClass_of_isBivariantClassComposition C G sZ sY sX i j hsi hsj hpp p q cloc
    (ConormalCompatibleVirtualNormalBundles.ofIsRegularImmersion i j hi hj) hc _
    (isBivariantClassComposition_bivariantComposite C G sZ sY sX i j hsi hsj p q _ _ hgys hgysc)

end Composition

end Stacks.Chow

end
