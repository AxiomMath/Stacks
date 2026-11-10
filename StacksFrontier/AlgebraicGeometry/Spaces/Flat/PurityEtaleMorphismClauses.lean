module

public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceEtaleTargetDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PurityEtaleMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat.PuritySchemeBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcomp

/-!
# Purity along an étale morphism over the base: the three clauses of Stacks 0CW3

Let `Y` be an algebraic space over a scheme `S`, let `f : X ⟶ Y` be decent and of finite type,
let `ℱ` be a finite type quasi-coherent `𝒪_X`-module and `y ∈ |Y|`, and let `g : X' ⟶ X` be an
étale morphism such that `X' ⟶ Y` is decent and of finite type.  Write `F = f^{-1}(\{y\})`.

1. If `Ass_{X/Y}(ℱ) ⊆ g(|X'|)` and `g^*ℱ` is (universally) pure above `y`, then `ℱ` is
   (universally) pure above `y`.
2. If `ℱ` is pure above `y`, `g(|X'|) ⊇ F`, and `Y` is affine local with closed point `y`, then
   `Ass_{X/Y}(ℱ) ⊆ g(|X'|)`.
3. If `ℱ` is pure above `y`, `ℱ` is flat over `Y` at all points of `F`,
   `g(|X'|) ⊇ Ass_{X/Y}(ℱ) ∩ F`, and `Y` is affine local with closed point `y`, then
   `Ass_{X/Y}(ℱ) ⊆ g(|X'|)`.

`StacksFrontier/AlgebraicGeometry/Spaces/Flat/PurityEtaleMorphism.lean` proves these for an
`AlgebraicGeometry.Space.EtaleOverSource`, a structure one of whose fields is quasi-coherence of
`g^*ℱ`; this file builds that structure from the source's data alone, quasi-coherence being
Stacks 03GA
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`),
and states the three clauses with exactly the source's hypotheses.

## Main definitions

* `AlgebraicGeometry.Space.EtaleOverSource.ofIsEtale`: the étale morphism over the source of a
  pre-pure situation built from the source's hypotheses.
* `AlgebraicGeometry.Space.ChartDiagram.postcompEtaleTarget`: a commuting square of étale scheme
  charts of `f`, with its target chart postcomposed with an étale morphism `ψ`, read as one of
  `f ≫ ψ`.

## Main results

* `AlgebraicGeometry.Space.isFlatOverAtPoint_comp_hom_of_isEtale`: flatness of a module over the
  target at a point survives postcomposing the morphism with an étale morphism of targets.
* `AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_iso`:
  Stacks 0CW1 for a target isomorphic to the algebraic space of a scheme of the site.
* `AlgebraicGeometry.Space.isPureAbove_of_isEtale_of_subset_range`: **Stacks 0CW3, clause (1)**,
  both readings.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_subset_range_of_isEtale`:
  **Stacks 0CW3, clause (2)**.
* `AlgebraicGeometry.Space.relativeWeaklyAssociatedPoints_subset_range_of_isEtale_of_isFlatOver`:
  **Stacks 0CW3, clause (3)**.

Clause (4) of the source reads "Add more here" and has no content.

## Implementation notes

Clause (3) needs Stacks 0CW1 at the point `y`.  The library proves 0CW1 at the source's
generality, a scheme base,
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`.
An affine local base `Y` comes with an isomorphism `e : h_T ≅ Y` from the algebraic space of a
scheme `T` of the site, and 0CW1 is transported along it: the relative weak assassin does not
change when the morphism is postcomposed with the étale `e⁻¹` (Stacks 0CUZ,
`AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale`), finiteness of
type is kept (Stacks 03XG and 06LT), and flatness of `ℱ` over the target at a point is kept,
because a chart square of `f` with target chart postcomposed with `e⁻¹` is a chart square of
`f ≫ e⁻¹` with the same source chart and the same vertical morphism.

## References

* [Stacks Project, Lemma 77.6.3 (Tag 0CW3)](https://stacks.math.columbia.edu/tag/0CW3)
* [Stacks Project, Tag 0CW1](https://stacks.math.columbia.edu/tag/0CW1)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Flatness over the target after an étale morphism of targets -/

/-- A commuting square of étale scheme charts of `f : X ⟶ Y`, with its target chart
postcomposed with an étale morphism `ψ : Y ⟶ Y'` (Stacks 03LP), read as a commuting square of
étale scheme charts of `f ≫ ψ`: the source chart and the vertical morphism are unchanged. -/
@[reducible] def ChartDiagram.postcompEtaleTarget {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y.1} (ψ : Y ⟶ Y') (hψ : IsEtale B S hS ψ.hom)
    (d : ChartDiagram B S hS X Y.1 f) : ChartDiagram B S hS X Y'.1 (f ≫ ψ.hom) where
  U := d.U
  V := (smallEtalePostcomp B S hS ψ hψ).obj d.V
  g := d.g
  comm := by
    change d.U.1.hom ≫ f ≫ ψ.hom = yoneda.map d.g ≫ d.V.1.hom ≫ ψ.hom
    rw [← Category.assoc, d.comm, Category.assoc]

/-- **Flatness over the target at a point survives an étale morphism of targets.** If an
`𝒪_X`-module `F` is flat over `Y` at a point `x` of `|X|` along `f : X ⟶ Y` (Stacks 05VV at a
point), then it is flat over `Y'` at `x` along `f ≫ ψ` for every étale `ψ : Y ⟶ Y'`: the
witnessing chart square, with its target chart postcomposed with `ψ`, witnesses the latter. -/
theorem isFlatOverAtPoint_comp_hom_of_isEtale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) {Y Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y.1)
    (ψ : Y ⟶ Y') (hψ : IsEtale B S hS ψ.hom) (F : Modules.{u, u} B S hS X hX)
    (x : points B S hS X) (h : IsFlatOverAtPoint B S hS hX f F x) :
    IsFlatOverAtPoint B S hS hX (f ≫ ψ.hom) F x := by
  obtain ⟨d, u, hu, hflat⟩ := h
  exact ⟨ChartDiagram.postcompEtaleTarget ψ hψ d, u, hu, hflat⟩

/-! ### Stacks 0CW1 over a base isomorphic to a scheme of the site -/

section Specialization

attribute [local instance] pointTopology

/-- **Stacks 0CW1 over a base isomorphic to a scheme of the site.** Let `X` be a decent
algebraic space, `f : X ⟶ Y` locally of finite type, where `Y` is isomorphic to the algebraic
space of a scheme `V` of the site, `F` a finite type quasi-coherent `𝒪_X`-module and `s ∈ |Y|`
such that `F` is flat over `Y` at every point of `|X|` above `s`.  A point of the relative weak
assassin `WeakAss_{X/Y}(F)` specializing to a point above `s` specializes to a point of
`WeakAss_{X/Y}(F)` above `s`.

This is
`AlgebraicGeometry.Space.exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase`
transported along the isomorphism; see the implementation notes of this file. -/
theorem exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_iso
    (V : BigFppfOver B S hS) {X Y : AlgebraicSpaces B S hS} (e : yoneda.obj V ≅ Y.1)
    (f : X ⟶ Y) (hXdec : IsDecentSpace B S hS X.1) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    [SheafOfModules.IsFiniteTypeOnSite F] (s : points B S hS Y.1)
    (hflat : ∀ t : points B S hS X.1, pointsMap B S hS X.1 f.hom t = s →
      IsFlatOverAtPoint B S hS X.2 f.hom F t)
    {x' : points B S hS X.1} (hx' : IsRelativeWeaklyAssociatedPoint B S hS f F x')
    (hmeets : ∃ t : points B S hS X.1, x' ⤳ t ∧ pointsMap B S hS X.1 f.hom t = s) :
    ∃ x : points B S hS X.1, x' ⤳ x ∧ pointsMap B S hS X.1 f.hom x = s ∧
      IsRelativeWeaklyAssociatedPoint B S hS f F x := by
  let ψinv : Y ⟶ schemeSpace V := ObjectProperty.homMk e.inv
  let ψ : schemeSpace V ⟶ Y := ObjectProperty.homMk e.hom
  have hψinv : IsEtale B S hS ψinv.hom := isEtale_of_isIso B S hS e.inv
  have hψ : IsEtale B S hS ψ.hom := isEtale_of_isIso B S hS e.hom
  let f' : X ⟶ schemeSpace V := f ≫ ψinv
  have hf'ψ : f' ≫ ψ = f := ObjectProperty.hom_ext _ (by
    change (f.hom ≫ e.inv) ≫ e.hom = f.hom
    rw [Category.assoc, e.inv_hom_id, Category.comp_id])
  have hass : ∀ z, IsRelativeWeaklyAssociatedPoint B S hS f' F z ↔
      IsRelativeWeaklyAssociatedPoint B S hS f F z := fun z => by
    rw [← isRelativeWeaklyAssociatedPoint_comp_iff_of_isEtale B S hS f' ψ hψ F z, hf'ψ]
  have hpt : ∀ z : points B S hS X.1, pointsMap B S hS X.1 f'.hom z =
      pointsMap B S hS Y.1 e.inv s ↔ pointsMap B S hS X.1 f.hom z = s := fun z => by
    change pointsMap B S hS X.1 (f.hom ≫ e.inv) z = _ ↔ _
    rw [pointsMap_comp_apply]
    have hinv : ∀ a, pointsMap B S hS (yoneda.obj V) e.hom (pointsMap B S hS Y.1 e.inv a) = a :=
      fun a => by rw [← pointsMap_comp_apply, e.inv_hom_id, pointsMap_id, id_eq]
    exact Function.LeftInverse.injective hinv |>.eq_iff
  have hf' : IsLocallyOfFiniteType B S hS f'.hom :=
    isLocallyOfFiniteType_comp' B S hS f.hom e.inv Y.2 (isAlgebraicSpace_yoneda B S hS V) hf
      (isLocallyOfFiniteType_of_isEtale' B S hS e.inv hψinv)
  obtain ⟨x, hspec, hxs, hxass⟩ :=
    exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_schemeBase B S hS V f' hXdec hf' F
      (pointsMap B S hS Y.1 e.inv s)
      (fun t ht => isFlatOverAtPoint_comp_hom_of_isEtale X.2 f.hom ψinv hψinv F t
        (hflat t ((hpt t).1 ht)))
      ((hass x').2 hx')
      (hmeets.imp fun t ht => ⟨ht.1, (hpt t).2 ht.2⟩)
  exact ⟨x, hspec, (hpt x).1 hxs, (hass x).1 hxass⟩

end Specialization

/-! ### The étale morphism over the source -/

/-- **The data of Stacks 0CW3 as an `AlgebraicGeometry.Space.EtaleOverSource`.** An étale
morphism `g : X' ⟶ X` into the source of a pre-pure situation with `X' ⟶ Y` decent and of finite
type. -/
@[reducible] noncomputable def EtaleOverSource.ofIsEtale (P : PrePureSituation.{u, u} B S hS)
    (X' : AlgebraicSpaces B S hS) (g : X' ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS))
    (hg : IsEtale B S hS g.hom) (hft : IsFiniteType B S hS (g.hom ≫ P.f))
    (hdec : IsDecent B S hS (g.hom ≫ P.f)) : EtaleOverSource P where
  X' := X'
  g := g
  isEtale := hg
  finiteType := hft
  decent := hdec

/-! ### The three clauses -/

section Clauses

attribute [local instance] pointTopology

variable (P : PrePureSituation.{u, u} B S hS) (X' : AlgebraicSpaces B S hS)
  (g : X' ⟶ (⟨P.X, P.hX⟩ : AlgebraicSpaces B S hS))

/-- **Stacks 0CW3, clause (1).** Let `Y` be an algebraic space over `S`, let `f : X ⟶ Y` be
decent and of finite type, `ℱ` a finite type quasi-coherent `𝒪_X`-module and `y ∈ |Y|` (the
pre-pure situation `P`), and let `g : X' ⟶ X` be étale with `X' ⟶ Y` decent and of finite type.
If `Ass_{X/Y}(ℱ) ⊆ g(|X'|)` and `g^*ℱ` is pure above `y`, then `ℱ` is pure above `y`; and if
`Ass_{X/Y}(ℱ) ⊆ g(|X'|)` and `g^*ℱ` is universally pure above `y`, then `ℱ` is universally
pure above `y`.

The situation on `X'` carrying `g^*ℱ` is
`(EtaleOverSource.ofIsEtale P X' g hg hft hdec).situation`. The relative assassin `Ass_{X/Y}(ℱ)`
is the relative weak assassin of Stacks 0CV0, which is the set the source writes `Ass_{X/Y}(ℱ)`
since `f` is of finite type. -/
@[stacks 0CW3 "clause (1), both the pure and the universally pure reading, under exactly the \
source's hypotheses"]
theorem isPureAbove_of_isEtale_of_subset_range (hg : IsEtale B S hS g.hom)
    (hft : IsFiniteType B S hS (g.hom ≫ P.f)) (hdec : IsDecent B S hS (g.hom ≫ P.f))
    (hass : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom)) :
    (IsPureAbove (EtaleOverSource.ofIsEtale P X' g hg hft hdec).situation → IsPureAbove P) ∧
      (IsUniversallyPureAbove (EtaleOverSource.ofIsEtale P X' g hg hft hdec).situation →
        IsUniversallyPureAbove P) :=
  ⟨(EtaleOverSource.ofIsEtale P X' g hg hft hdec).isPureAbove_of_isPureAbove_situation hass,
    (EtaleOverSource.ofIsEtale P X' g hg hft
      hdec).isUniversallyPureAbove_of_isUniversallyPureAbove_situation hass⟩

/-- **Stacks 0CW3, clause (2).** In the situation of clause (1), if `ℱ` is pure above `y`, the
image `g(|X'|)` contains the fibre `F = f^{-1}(\{y\})`, and `Y` is affine local with closed point
`y`, then `Ass_{X/Y}(ℱ) ⊆ g(|X'|)`.

The proof is the source's: the image of an étale morphism is open (Stacks 03IR), and purity
over the affine local base specializes every point of `Ass_{X/Y}(ℱ)` into `F`
(`AlgebraicGeometry.Space.purityFibreSpecialization`).  Decency and finiteness of type of
`X' ⟶ Y`, which the source assumes throughout the lemma, are not used by this clause, so the
statement omits them and is that much more general. -/
@[stacks 0CW3 "clause (2), under exactly the source's hypotheses"]
theorem relativeWeaklyAssociatedPoints_subset_range_of_isEtale (hg : IsEtale B S hS g.hom)
    (hpure : IsPureAbove P)
    (hfibre : pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆ Set.range (pointsMap B S hS X'.1 g.hom))
    (hlocal : P.IsAffineLocalAt) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom) := by
  intro x hx
  obtain ⟨θ, hspec, hθ⟩ := purityFibreSpecialization P hlocal hpure x hx
  exact hspec.mem_open (isOpen_range_pointsMap_of_isEtale B S hS g.hom X'.2 P.hX hg)
    (hfibre hθ)

/-- **Stacks 0CW3, clause (3).** In the situation of clause (1), if `ℱ` is pure above `y`, `ℱ`
is flat over `Y` at all points of the fibre `F = f^{-1}(\{y\})` (Stacks 05VV at a point), the
image `g(|X'|)` contains `Ass_{X/Y}(ℱ) ∩ F`, and `Y` is affine local with closed point `y`, then
`Ass_{X/Y}(ℱ) ⊆ g(|X'|)`.

As in the source: the image of an étale morphism is open (Stacks 03IR), purity over the affine
local base specializes every point of `Ass_{X/Y}(ℱ)` into `F`
(`AlgebraicGeometry.Space.purityFibreSpecialization`), and Stacks 0CW1 over the base, which is
isomorphic to a scheme of the site, improves that to a specialization into
`Ass_{X/Y}(ℱ) ∩ F`.  As for clause (2), decency and finiteness of type of `X' ⟶ Y` are not used,
so the statement omits them and is that much more general. -/
@[stacks 0CW3 "clause (3), under exactly the source's hypotheses; flatness is flatness of the \
module over Y at the points of the fibre, as in the source"]
theorem relativeWeaklyAssociatedPoints_subset_range_of_isEtale_of_isFlatOver
    (hg : IsEtale B S hS g.hom) (hpure : IsPureAbove P)
    (hflat : ∀ t : points B S hS P.X, pointsMap B S hS P.X P.f t = P.y →
      IsFlatOverAtPoint B S hS P.hX P.f P.F t)
    (hfibre : relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ∩
        pointsMap B S hS P.X P.f ⁻¹' {P.y} ⊆ Set.range (pointsMap B S hS X'.1 g.hom))
    (hlocal : P.IsAffineLocalAt) :
    relativeWeaklyAssociatedPoints B S hS P.structureSpaceMorphism P.F ⊆
      Set.range (pointsMap B S hS X'.1 g.hom) := by
  obtain ⟨T, -, -, -, ⟨e⟩⟩ := hlocal.1
  have hXdec : IsDecentSpace B S hS P.X :=
    isDecentSpace_of_isDecent B S hS P.hX P.hY P.f
      (isDecentSpace_of_iso B S hS e (isDecentSpace_yoneda B S hS T)) P.decent
  intro x hx
  obtain ⟨θ, hspec, hθy, hθass⟩ :=
    exists_specializes_isRelativeWeaklyAssociatedPoint_fibre_of_iso T
      (X := ⟨P.X, P.hX⟩) (Y := ⟨P.Y, P.hY⟩) e P.structureSpaceMorphism hXdec
      P.finiteType.1 P.F P.y hflat hx (purityFibreSpecialization P hlocal hpure x hx)
  exact hspec.mem_open (isOpen_range_pointsMap_of_isEtale B S hS g.hom X'.2 P.hX hg)
    (hfibre ⟨hθass, hθy⟩)

end Clauses

end AlgebraicGeometry.Space

end
