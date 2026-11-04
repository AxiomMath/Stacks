module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseChangeQuasicoherent
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.FibreDimensionStalkVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Top-degree cohomology of a fibre, over an affine open of the base

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, let `V ⊆ Y` be an affine open and let `d`
be a degree above which the higher direct images along `f ∣_ V` of every quasi-coherent module
vanish — the situation [Stacks, Tag 0E7D] part (2) produces around a point whose fibre has
dimension at most `d`. This file compares `Hᵈ` of the structure sheaf of a fibre over a point of
`V` with `Hᵈ` over `f⁻¹V`, and with `Hᵈ` of the fibre of a base change.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofVanishing`: the top-degree base-change
  situation of a morphism whose higher direct images vanish above `d`, along an arbitrary
  cartesian square — the shape in which [Stacks, Tag 0E7D] part (2) supplies the vanishing.

## Main results

All in the namespace `Stacks.AlgebraicGeometry.TopDegreeBaseChange`.

* `exists_isPullback_fiberToSpecResidueField_morphismRestrict`: the fibre of `f` over a point
  of an open `V` is a fibre of `f ∣_ V`.
* `isZero_rightDerived_unit_fiber_of_isZero_restrict`: `Hᵈ(f⁻¹V, 𝒪) = 0` forces
  `Hᵈ(X_y, 𝒪_{X_y}) = 0` for every `y ∈ V`.
* `isZero_rightDerived_unit_fiber_of_isZero_fiber_baseChange`: for `g : Y' ⟶ Y` and `y'` over
  `y ∈ V`, the vanishing of `Hᵈ` of the fibre of the base change at `y'` forces the vanishing of
  `Hᵈ(X_y, 𝒪_{X_y})`, the residue field extension `κ(y) ⟶ κ(y')` being faithfully flat.
* `isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict` and
  `isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict_baseChange`: the two parts of
  [Stacks, Tag 0E7F] over such an affine open `V`, at fibre dimension one.
* `isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage` and
  `isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage_baseChange`:
  parts (1) and (2) of [Stacks, Tag 0E7F], with no hypothesis beyond the tag's own; the open `V`
  is supplied by [Stacks, Tag 0E7D] part (2)
  (`exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le`).

## Implementation notes

The source proves [Stacks, Tag 0E7F] by quoting that `R¹ f_* 𝒪_X` is of finite type
([Stacks, Tag 0EX4]) and that its formation commutes with arbitrary base change
([Stacks, Tag 0E7D] through [Stacks, Tag 0EX3]). Neither is needed in that generality. Every base
change the argument performs, once [Stacks, Tag 0E7D] part (2) has shrunk `Y` to an affine open
`V`, is an **affine base change of an affine base** — to `Spec κ(y)`, to an affine open `W ∋ y'`
of `Y'` lying over `V`, to `Spec κ(y')` — and for those conclusion (c) of [Stacks, Tag 0EX3] is
`AffineBaseChangeQuasicoherent.lean`'s `affineTopDegreeTensorBaseChangeIso`. The finite-type
clause enters the source only through Nakayama's lemma, to pass from the vanishing after the base
change `g` back to `y`; at the fibre that passage is the faithful flatness of the field extension
`κ(y) ⟶ κ(y')`, which needs no finiteness.

The registrations in `ContractingRationalCurves.lean` carry the two clauses as hypotheses; the
two statements here prove the same conclusions without them, under the same notation
`firstDirectImageStructureSheaf` and `firstCohomologyStructureSheaf`.

`moduleGlobalSections` is written with its namespace, because the import of
`FibreDimensionStalkVanishing.lean` brings a second declaration of that name into scope.

Cohomology is the `ℕ`-indexed `CategoryTheory.Functor.rightDerived` in the intermediate
statements, which is the indexing of `AffineBaseChangeQuasicoherent.lean`;
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` crosses to the `ℤ`-indexed
`rightDerivedPlus` of `firstCohomologyStructureSheaf` at the end.

## References

* [Stacks Project, Tag 0E7F](https://stacks.math.columbia.edu/tag/0E7F)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry

attribute [local instance 2000] HasDerivedCategory.standard

noncomputable section

/-- **A top-degree base-change situation from the vanishing itself.** Where
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom` meets the vanishing field
from the acyclicity of an affine morphism, this one takes it as the hypothesis it is, which is
the shape [Stacks, Tag 0E7D] part (2) supplies it in; the cartesian square is an argument. -/
abbrev TopDegreeBaseChangeSituation.ofVanishing {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [CompactSpace (X : Type u)] [QuasiSeparatedSpace (X : Type u)]
    [CompactSpace (Y : Type u)] [QuasiSeparatedSpace (Y : Type u)]
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus i).obj F))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (sq : IsPullback g' f' f g) :
    TopDegreeBaseChangeSituation.{u} where
  X := X
  Y := Y
  f := f
  d := d
  isCompact_X := ‹CompactSpace (X : Type u)›
  isQuasiSeparated_X := ‹QuasiSeparatedSpace (X : Type u)›
  isCompact_Y := ‹CompactSpace (Y : Type u)›
  isQuasiSeparated_Y := ‹QuasiSeparatedSpace (Y : Type u)›
  vanishes_above := hvan
  X' := X'
  Y' := Y'
  g' := g'
  f' := f'
  g := g
  isPullback := sq

namespace TopDegreeBaseChange

/-- **The fibre square over a point of an open of the base.** The morphism `Spec κ(y) ⟶ Y` has
image `{y}`, so it factors through any open `V` containing `y`
(`AlgebraicGeometry.IsOpenImmersion.lift`), and over that factorization the fibre of `f` at `y`
is a fibre product of the *restriction* `f ∣_ V`: the fibre square of `f` is the paste of this
square with the cartesian square of the restriction, so the left-hand square of the paste is
cartesian. -/
theorem exists_isPullback_fiberToSpecResidueField_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (y : Y) (hy : y ∈ V) :
    ∃ (h : Spec (Y.residueField y) ⟶ V.toScheme) (q : f.fiber y ⟶ (f ⁻¹ᵁ V).toScheme),
      IsPullback q (f.fiberToSpecResidueField y) (f ∣_ V) h := by
  have hrange : Set.range (Y.fromSpecResidueField y) ⊆ Set.range V.ι := by
    rw [Scheme.range_fromSpecResidueField, Scheme.Opens.range_ι]
    simpa using hy
  have souter : IsPullback (f.fiberι y) (f.fiberToSpecResidueField y) f
      (IsOpenImmersion.lift V.ι (Y.fromSpecResidueField y) hrange ≫ V.ι) := by
    rw [IsOpenImmersion.lift_fac]
    exact IsPullback.of_hasPullback f (Y.fromSpecResidueField y)
  exact ⟨_, _, IsPullback.of_right' souter (isPullback_morphismRestrict f V).flip⟩

/-- **The vanishing above `d` passes to the cohomology over an affine base.** Over an affine
base the higher direct image and the absolute cohomology of a quasi-coherent module vanish
together ([Stacks, Tag 01XK]), so the vanishing of the higher direct images above `d` is the
vanishing of `Hᵈ⁺¹` of every quasi-coherent module, which is the form
`AffineBaseChangeQuasicoherent.lean` asks for. -/
theorem isZero_cohomology_succ_of_vanishing {X₀ Y₀ : Scheme.{u}} (g : X₀ ⟶ Y₀) [QuasiCompact g]
    [QuasiSeparated g] [IsAffine Y₀] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : X₀.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward g).rightDerivedPlus i).obj F))
    (G : X₀.Modules) (hG : G.IsQuasicoherent) :
    IsZero (((Cohomology.AffineBase.moduleGlobalSections X₀).rightDerivedPlus
      ((d : ℤ) + 1)).obj G) :=
  have := hG
  isZero_cohomology_of_isZero_rightDerivedPlus_pushforward g _ G (hvan _ (by omega) G hG)

/-- **The pullback of the structure sheaf vanishes in cohomology exactly when the structure sheaf
does.** `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` identifies the two. -/
theorem isZero_rightDerived_pullback_unit_iff {Z Z' : Scheme.{u}} (q : Z ⟶ Z') (d : ℕ) :
    IsZero (((Cohomology.AffineBase.moduleGlobalSections Z).rightDerived d).obj
        ((Scheme.Modules.pullback q).obj (SheafOfModules.unit Z'.ringCatSheaf))) ↔
      IsZero (((Cohomology.AffineBase.moduleGlobalSections Z).rightDerived d).obj
        (SheafOfModules.unit Z.ringCatSheaf)) :=
  (((Cohomology.AffineBase.moduleGlobalSections Z).rightDerived d).mapIso
    (Scheme.Modules.pullbackUnitIso q)).isZero_iff

section Restrict

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) [IsAffine V.toScheme]
    [QuasiCompact (f ∣_ V)] [QuasiSeparated (f ∣_ V)] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : (f ⁻¹ᵁ V).toScheme.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F))

include hvan

/-- **The cohomology of a fibre over a point of an affine open of the base.** If the higher
direct images along `f ∣_ V` vanish above `d` and `Hᵈ(f⁻¹V, 𝒪) = 0`, then `Hᵈ(X_y, 𝒪) = 0` for
every `y ∈ V`.

The fibre is the base change of `f⁻¹V ⟶ V ≅ Spec Γ(V, ⊤)` along the spectrum of the ring map
`Γ(V, ⊤) ⟶ κ(y)` (`exists_isPullback_fiberToSpecResidueField_morphismRestrict`), so this is the
vanishing form of conclusion (c) of [Stacks, Tag 0EX3] over an affine base,
`isZero_rightDerived_pullback_baseChange`, at the structure sheaf. -/
theorem isZero_rightDerived_unit_fiber_of_isZero_restrict
    (h : IsZero (((Cohomology.AffineBase.moduleGlobalSections (f ⁻¹ᵁ V).toScheme).rightDerived
      d).obj (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)))
    (y : Y) (hy : y ∈ V) :
    IsZero (((Cohomology.AffineBase.moduleGlobalSections (f.fiber y)).rightDerived d).obj
      (SheafOfModules.unit (f.fiber y).ringCatSheaf)) := by
  obtain ⟨hV, q, sq1⟩ := exists_isPullback_fiberToSpecResidueField_morphismRestrict f V y hy
  let W : Over (Spec (CommRingCat.of Γ(V.toScheme, ⊤))) :=
    Over.mk ((f ∣_ V) ≫ V.toScheme.isoSpec.hom)
  have : QuasiCompact W.hom := inferInstanceAs (QuasiCompact ((f ∣_ V) ≫ _))
  have : QuasiSeparated W.hom := inferInstanceAs (QuasiSeparated ((f ∣_ V) ≫ _))
  have tiso : IsPullback (f ∣_ V) (𝟙 (f ⁻¹ᵁ V).toScheme) V.toScheme.isoSpec.hom
      ((f ∣_ V) ≫ V.toScheme.isoSpec.hom) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have sq := IsPullback.paste_vert sq1.flip tiso
  rw [Category.comp_id, ← Spec.map_preimage (hV ≫ V.toScheme.isoSpec.hom)] at sq
  exact (isZero_rightDerived_pullback_unit_iff q d).mp
    (isZero_rightDerived_pullback_baseChange Γ(V.toScheme, ⊤) W d
      ⟨SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf,
        Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _⟩
      (isZero_cohomology_succ_of_vanishing (f ∣_ V) d hvan) _ q (f.fiberToSpecResidueField y)
      sq h)

end Restrict

/-- **A field extension is faithfully flat.** A nonzero module over a field is free and
nontrivial. -/
@[ega "0 6.4.2" "special case", ega "IV 8.1.2" "partial", ega "IV 9.1.3" "more general"]
theorem faithfullyFlat_of_field {K L : CommRingCat.{u}} (hK : IsField K) [Nontrivial L]
    (φ : K ⟶ L) : φ.hom.FaithfullyFlat := by
  let : Field K := hK.toField
  let : Algebra K L := φ.hom.toAlgebra
  exact (inferInstance : Module.FaithfullyFlat K L)

section BaseChange

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (V : Y.Opens)
    [IsAffine V.toScheme] (d : ℕ)
    (hvan : ∀ i : ℤ, (d : ℤ) < i → ∀ F : (f ⁻¹ᵁ V).toScheme.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F))

include hvan

/-- **The vanishing above `d` along a fibre over a point of `V`.** The fibre morphism
`X_y ⟶ Spec κ(y)` is a base change of `f ∣_ V`, so conclusion (a) of [Stacks, Tag 0EX3]
(`isZero_rightDerivedPlus_pushforward_baseChange`) carries the vanishing to it. -/
theorem vanishing_fiberToSpecResidueField (y : Y) (hy : y ∈ V) :
    ∀ i : ℤ, (d : ℤ) < i → ∀ F : (f.fiber y).Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward (f.fiberToSpecResidueField y)).rightDerivedPlus i).obj
        F) := by
  obtain ⟨hV, q, sq1⟩ := exists_isPullback_fiberToSpecResidueField_morphismRestrict f V y hy
  have : CompactSpace ((f ⁻¹ᵁ V).toScheme : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  have : QuasiSeparatedSpace ((f ⁻¹ᵁ V).toScheme : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  intro i hi F hF
  have := hF
  exact @isZero_rightDerivedPlus_pushforward_baseChange
    (TopDegreeBaseChangeSituation.ofVanishing (f ∣_ V) d hvan q
      (f.fiberToSpecResidueField y) hV sq1) i hi F hF

/-- **Descent of the vanishing of `Hᵈ` of a fibre along a base change.** Let `g : Y' ⟶ Y` and let
`y'` map to a point of `V`. If `Hᵈ` of the structure sheaf of the fibre of the base change
`f' : X ×_Y Y' ⟶ Y'` at `y'` vanishes, then so does `Hᵈ(X_{g y'}, 𝒪)`.

The fibre of `f'` at `y'` is the base change of `X_{g y'} ⟶ Spec κ(g y')` along the field
extension `κ(g y') ⟶ κ(y')` (`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`),
the cohomology of `X_{g y'}` vanishes above `d` by `vanishing_fiberToSpecResidueField`, and a field
extension is faithfully flat, so `isZero_rightDerived_of_isZero_pullback_baseChange` applies. -/
theorem isZero_rightDerived_unit_fiber_of_isZero_fiber_baseChange {Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (y' : Y') (hy : g y' ∈ V)
    (h : IsZero (((Cohomology.AffineBase.moduleGlobalSections
      ((pullback.snd f g).fiber y')).rightDerived d).obj
        (SheafOfModules.unit ((pullback.snd f g).fiber y').ringCatSheaf))) :
    IsZero (((Cohomology.AffineBase.moduleGlobalSections (f.fiber (g y'))).rightDerived d).obj
      (SheafOfModules.unit (f.fiber (g y')).ringCatSheaf)) := by
  let W : Over (Spec (CommRingCat.of (Y.residueField (g y')))) :=
    Over.mk (f.fiberToSpecResidueField (g y'))
  have : QuasiCompact (f.fiberToSpecResidueField (g y')) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField (g y'))) ‹_›
  have : QuasiSeparated (f.fiberToSpecResidueField (g y')) :=
    MorphismProperty.of_isPullback (P := @QuasiSeparated)
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField (g y'))) ‹_›
  have : QuasiCompact W.hom := ‹QuasiCompact (f.fiberToSpecResidueField (g y'))›
  have : QuasiSeparated W.hom := ‹QuasiSeparated (f.fiberToSpecResidueField (g y'))›
  exact isZero_rightDerived_of_isZero_pullback_baseChange (Y.residueField (g y')) W d
    ⟨SheafOfModules.unit (f.fiber (g y')).ringCatSheaf,
      Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit _⟩
    (isZero_cohomology_succ_of_vanishing (f.fiberToSpecResidueField (g y')) d
      (vanishing_fiberToSpecResidueField f V d hvan (g y') hy)) (g.residueFieldMap y')
    (faithfullyFlat_of_field (Field.toIsField (Y.residueField (g y'))) _) _ _
    (AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback
      (IsPullback.of_hasPullback f g) y').flip
    ((isZero_rightDerived_pullback_unit_iff _ d).mpr h)

end BaseChange

section FirstCohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (V : Y.Opens) [IsAffine V.toScheme]
    (hvan : ∀ i : ℤ, ((1 : ℕ) : ℤ) < i → ∀ F : (f ⁻¹ᵁ V).toScheme.Modules, F.IsQuasicoherent →
      IsZero (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus i).obj F))

include hvan

/-- **Part (1) of [Stacks, Tag 0E7F] over an affine open on which the higher direct images vanish
above one.** If `R¹ f_* 𝒪_X = 0` then `H¹(X_y, 𝒪_{X_y}) = 0` for every `y ∈ V`.

Over the affine base `V` the vanishing of `R¹ (f ∣_ V)_* 𝒪`, which is the restriction of
`R¹ f_* 𝒪_X`, is the vanishing of `H¹(f⁻¹V, 𝒪)` ([Stacks, Tag 01XK]), and
`isZero_rightDerived_unit_fiber_of_isZero_restrict` passes to the fibre. -/
theorem isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict
    (hR : IsZero (firstDirectImageStructureSheaf f)) (y : Y) (hy : y ∈ V) :
    IsZero (firstCohomologyStructureSheaf (f.fiber y)) := by
  have hcoh : IsZero (((Cohomology.AffineBase.moduleGlobalSections
      (f ⁻¹ᵁ V).toScheme).rightDerivedPlus ((1 : ℕ) : ℤ)).obj
        (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)) :=
    isZero_cohomology_of_isZero_rightDerivedPlus_pushforward (f ∣_ V) 1
      (SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)
      (isZero_firstDirectImage_structureSheaf_restrict f V hR)
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Cohomology.AffineBase.moduleGlobalSections (f.fiber y)) 1 _).1
    (isZero_rightDerived_unit_fiber_of_isZero_restrict f V 1 hvan
      ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
        (Cohomology.AffineBase.moduleGlobalSections (f ⁻¹ᵁ V).toScheme) 1 _).2 hcoh) y hy)

/-- **Part (2) of [Stacks, Tag 0E7F] over an affine open on which the higher direct images vanish
above one.** Let `g : Y' ⟶ Y` and `y' ∈ Y'` with `g y' ∈ V`. If the base change
`f' : X ×_Y Y' ⟶ Y'` has `R¹ f'_* 𝒪_{X'} = 0`, then `H¹(X_{g y'}, 𝒪) = 0`.

Choose an affine open `W ∋ y'` inside `g⁻¹V`. The restriction of `f'` over `W` is the base change
of `f ∣_ V` along `W ⟶ V`, so its higher direct images vanish above one by conclusion (a) of
[Stacks, Tag 0EX3], and part (1)'s argument over `W` gives `H¹` of the fibre of `f'` at `y'`;
`isZero_rightDerived_unit_fiber_of_isZero_fiber_baseChange` descends it along
`κ(g y') ⟶ κ(y')`. -/
theorem isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict_baseChange
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (y' : Y') (hy : g y' ∈ V)
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f g))) :
    IsZero (firstCohomologyStructureSheaf (f.fiber (g y'))) := by
  have : IsProper (pullback.snd f g) :=
    MorphismProperty.of_isPullback (P := @IsProper) (IsPullback.of_hasPullback f g) ‹_›
  obtain ⟨W, hWaff, hy'W, hWV⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (X := Y') (x := y') (U := g ⁻¹ᵁ V) hy
  have : IsAffine W.toScheme := hWaff
  have : CompactSpace ((f ⁻¹ᵁ V).toScheme : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  have : QuasiSeparatedSpace ((f ⁻¹ᵁ V).toScheme : Type u) :=
    quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)
  -- `W.ι ≫ g` factors through `V`, and the restriction of the base change of `f` over `W` is a
  -- base change of `f ∣_ V` along that factorization.
  have hrW : Set.range (W.ι ≫ g) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro - ⟨w, rfl⟩
    exact hWV w.2
  have souterW : IsPullback
      ((pullback.snd f g ⁻¹ᵁ W).ι ≫ pullback.fst f g) (pullback.snd f g ∣_ W) f
      (IsOpenImmersion.lift V.ι (W.ι ≫ g) hrW ≫ V.ι) := by
    rw [IsOpenImmersion.lift_fac]
    exact IsPullback.paste_horiz (isPullback_morphismRestrict (pullback.snd f g) W).flip
      (IsPullback.of_hasPullback f g)
  have sqW := IsPullback.of_right' souterW (isPullback_morphismRestrict f V).flip
  have hvanW : ∀ i : ℤ, ((1 : ℕ) : ℤ) < i →
      ∀ F : (pullback.snd f g ⁻¹ᵁ W).toScheme.Modules, F.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward (pullback.snd f g ∣_ W)).rightDerivedPlus i).obj
          F) := fun i hi F hF =>
    have := hF
    @isZero_rightDerivedPlus_pushforward_baseChange
      (TopDegreeBaseChangeSituation.ofVanishing (f ∣_ V) 1 hvan _
        (pullback.snd f g ∣_ W) _ sqW) i hi F hF
  have hfib : IsZero (firstCohomologyStructureSheaf ((pullback.snd f g).fiber y')) :=
    isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict (pullback.snd f g) W hvanW
      hR y' hy'W
  exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
      (Cohomology.AffineBase.moduleGlobalSections (f.fiber (g y'))) 1 _).1
    (isZero_rightDerived_unit_fiber_of_isZero_fiber_baseChange f V 1 hvan g y' hy
      ((Stacks.DerivedIndexing.isZero_rightDerived_obj_iff
        (Cohomology.AffineBase.moduleGlobalSections ((pullback.snd f g).fiber y')) 1 _).2 hfib))

end FirstCohomology

section Tag0E7F

variable {X Y : Scheme.{u}}

/-- **[Stacks, Tag 0E7F], part (1).** Let `f : X ⟶ Y` be proper and let `y ∈ Y` be a point whose
fibre has dimension at most one. If `R¹ f_* 𝒪_X = 0`, then `H¹(X_y, 𝒪_{X_y}) = 0`.

[Stacks, Tag 0E7D] part (2) shrinks `Y` to an affine open `V ∋ y` above which the higher direct
images of quasi-coherent modules vanish in degrees above one, and
`isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict` concludes over `V`. -/
@[stacks 0E7F "part (1)", ega "III 7.9.10.1" "partial"]
theorem isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    (hR : IsZero (firstDirectImageStructureSheaf f)) :
    IsZero (firstCohomologyStructureSheaf (f.fiber y)) := by
  obtain ⟨V, hyV, hVaff, -, -, -, -, hvan, -⟩ :=
    exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le f y 1 hdim
  have : IsAffine V.toScheme := hVaff
  exact isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict f V hvan hR y hyV

/-- **[Stacks, Tag 0E7F], part (2).** Let `f : X ⟶ Y` be proper and let `y ∈ Y` be a point whose
fibre has dimension at most one. If there is a morphism `g : Y' ⟶ Y` with `y` in its image such
that the base change `f' : X ×_Y Y' ⟶ Y'` of `f` by `g` has `R¹ f'_* 𝒪_{X'} = 0`, then
`H¹(X_y, 𝒪_{X_y}) = 0`.

[Stacks, Tag 0E7D] part (2) shrinks `Y` to an affine open `V ∋ y` above which the higher direct
images of quasi-coherent modules vanish in degrees above one, and
`isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict_baseChange` concludes over
`V`. -/
@[stacks 0E7F "part (2)", ega "III 7.9.10.1" "partial"]
theorem isZero_firstCohomologyStructureSheaf_fiber_of_isZero_firstDirectImage_baseChange
    (f : X ⟶ Y) [IsProper f] (y : Y)
    (hdim : topologicalKrullDim (f.fiber y) ≤ ((1 : ℕ) : WithBot ℕ∞))
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (hy : y ∈ Set.range g)
    (hR : IsZero (firstDirectImageStructureSheaf (pullback.snd f g))) :
    IsZero (firstCohomologyStructureSheaf (f.fiber y)) := by
  obtain ⟨y', rfl⟩ := hy
  obtain ⟨V, hyV, hVaff, -, -, -, -, hvan, -⟩ :=
    exists_isAffineOpen_topDegreeBaseChange_of_topologicalKrullDim_fiber_le f (g y') 1 hdim
  have : IsAffine V.toScheme := hVaff
  exact isZero_firstCohomologyStructureSheaf_fiber_of_vanishing_restrict_baseChange f V hvan g y'
    hyV hR

end Tag0E7F

end TopDegreeBaseChange

end

end Stacks.AlgebraicGeometry

end
