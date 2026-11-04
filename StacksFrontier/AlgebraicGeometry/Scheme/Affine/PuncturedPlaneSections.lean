module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Affine.PuncturedPlane

/-!
# Sections on the punctured affine plane

Over a field `k`, restriction of sections of the punctured affine plane to the two standard
coordinate opens, read through the canonical identification of the sections on a standard open
with a localization, gives a sequence

`Γ(U, 𝒪_U) → k[x, y, 1/x] × k[x, y, 1/y] → k[x, y, 1/xy]`

whose first map is injective and whose image is exactly the kernel of the second, the difference
of the two canonical localization maps. Computing that kernel identifies the global sections of
the punctured plane with the polynomial ring `k[x, y]` itself: a function regular away from the
origin is regular everywhere.

## Main definitions

* `AlgebraicGeometry.xCoordinate`, `AlgebraicGeometry.yCoordinate`: the two coordinate
  polynomials.
* `AlgebraicGeometry.sectionsToLocalization`: restriction of global sections to a standard open
  contained in the punctured plane, followed by the canonical identification of its sections with
  a localization, and `AlgebraicGeometry.restrictToX`, `AlgebraicGeometry.restrictToY`,
  `AlgebraicGeometry.restrictionPair` its two coordinate instances and their product.
* `AlgebraicGeometry.localizeXToXY`, `AlgebraicGeometry.localizeYToXY`: the canonical maps into
  the localization away from the product of the coordinates, and
  `AlgebraicGeometry.localizationDifference` their difference.

## Main results

* `AlgebraicGeometry.PuncturedAffinePlane.isIso_app_basicOpen`: on a standard open contained in
  the punctured plane, the comparison map of the canonical open immersion is an isomorphism.
* `AlgebraicGeometry.restrictionPair_injective`: exactness at the global sections.
* `AlgebraicGeometry.restrictionPair_exact`: exactness at the product of the two localizations.
* `AlgebraicGeometry.isIso_coordinateRingToGlobalSections`: the canonical map from `k[x, y]` to
  the global sections of the punctured plane is an isomorphism.

## Implementation notes

The rings written `k[x, y, 1/x]`, `k[x, y, 1/y]` and `k[x, y, 1/xy]` are `Localization.Away`.
The first arrow of the sequence is the honest sheaf restriction, transported through the
canonical localization identification on each standard open; the inverse transport is what makes
the sheaf axiom usable on it, and injectivity together with `Function.Exact` records the two
exactness assertions.

Surjectivity onto the kernel is a divisibility computation in `k[x, y]`: a pair of fractions
agreeing in `k[x, y, 1/xy]` has a common polynomial numerator, because `x` is prime and does not
divide `y`.

The standard opens of the punctured plane are preimages of standard opens of `Spec k[x, y]`, and
the two descriptions agree definitionally but not syntactically. The crossing is therefore made
once, at the level of terms: the sections maps on the three standard opens are restated on
`PuncturedAffinePlane.xOpen`, `PuncturedAffinePlane.yOpen` and `PuncturedAffinePlane.xyOpen` by
type ascription, and the naturality squares relating them are assembled with `congrArg` and
`Eq.trans` rather than by rewriting. Everything downstream is then syntactically in the shape the
sheaf condition and the rewriting tactics expect.

## References

* [Stacks Project, Tag 01IL](https://stacks.math.columbia.edu/tag/01IL)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The first coordinate polynomial on the affine plane. -/
abbrev xCoordinate (S : PuncturedAffinePlane.{u}) : S.R :=
  MvPolynomial.X 0

/-- The second coordinate polynomial on the affine plane. -/
abbrev yCoordinate (S : PuncturedAffinePlane.{u}) : S.R :=
  MvPolynomial.X 1

namespace PuncturedAffinePlane

private instance (S : PuncturedAffinePlane.{u}) : IsOpenImmersion S.openImmersion := by
  dsimp [PuncturedAffinePlane.openImmersion]
  infer_instance

/-- On a standard open contained in the punctured plane, the comparison map of the canonical open
immersion is an isomorphism: the sections of the punctured plane there are the sections of the
affine plane there. -/
theorem isIso_app_basicOpen (S : PuncturedAffinePlane.{u}) {f : S.R}
    (hf : (PrimeSpectrum.basicOpen f : S.X.Opens) ≤ S.U) :
    IsIso (S.openImmersion.app (PrimeSpectrum.basicOpen f)) :=
  S.openImmersion.isIso_app _ (by
    have hrange : S.openImmersion.opensRange = S.U := S.U.opensRange_ι
    rw [hrange]
    exact hf)

end PuncturedAffinePlane

/-- Restriction from the punctured plane to a standard open, expressed in the canonical
localization coordinates. -/
noncomputable def sectionsToLocalization (S : PuncturedAffinePlane.{u})
    (f : S.R) (hf : (PrimeSpectrum.basicOpen f : S.X.Opens) ≤ S.U) :
    Γ(S.puncturedScheme, ⊤) →+* Localization.Away f :=
  (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f)))).symm.toRingHom.comp
    ((@CategoryTheory.inv _ _ _ _ (S.openImmersion.app (PrimeSpectrum.basicOpen f))
        (S.isIso_app_basicOpen hf)).hom.comp
      (S.puncturedScheme.presheaf.map (homOfLE le_top).op).hom)

/-- Restriction to the first-coordinate standard open in localization coordinates. -/
noncomputable def restrictToX (S : PuncturedAffinePlane.{u}) :
    Γ(S.puncturedScheme, ⊤) →+* Localization.Away (xCoordinate S) :=
  sectionsToLocalization S (xCoordinate S) (S.basicOpen_X_le_U 0)

/-- Restriction to the second-coordinate standard open in localization coordinates. -/
noncomputable def restrictToY (S : PuncturedAffinePlane.{u}) :
    Γ(S.puncturedScheme, ⊤) →+* Localization.Away (yCoordinate S) :=
  sectionsToLocalization S (yCoordinate S) (S.basicOpen_X_le_U 1)

/-- The product of the two canonical restriction maps. -/
noncomputable def restrictionPair (S : PuncturedAffinePlane.{u}) :
    Γ(S.puncturedScheme, ⊤) →+*
      (Localization.Away (xCoordinate S) × Localization.Away (yCoordinate S)) :=
  RingHom.prod (restrictToX S) (restrictToY S)

/-- The canonical map from the localization at `x` to the localization at `xy`. -/
noncomputable def localizeXToXY (S : PuncturedAffinePlane.{u}) :
    Localization.Away (xCoordinate S) →+*
      Localization.Away (xCoordinate S * yCoordinate S) :=
  IsLocalization.Away.lift
      (P := Localization.Away (xCoordinate S * yCoordinate S))
      (g := algebraMap S.R (Localization.Away (xCoordinate S * yCoordinate S)))
      (xCoordinate S) <| by
    apply isUnit_of_mul_isUnit_left (y :=
      algebraMap S.R (Localization.Away (xCoordinate S * yCoordinate S)) (yCoordinate S))
    simpa only [map_mul] using
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (xCoordinate S * yCoordinate S))
        (xCoordinate S * yCoordinate S))

/-- The canonical map from the localization at `y` to the localization at `xy`. -/
noncomputable def localizeYToXY (S : PuncturedAffinePlane.{u}) :
    Localization.Away (yCoordinate S) →+*
      Localization.Away (xCoordinate S * yCoordinate S) :=
  IsLocalization.Away.lift
      (P := Localization.Away (xCoordinate S * yCoordinate S))
      (g := algebraMap S.R (Localization.Away (xCoordinate S * yCoordinate S)))
      (yCoordinate S) <| by
    apply isUnit_of_mul_isUnit_right (x :=
      algebraMap S.R (Localization.Away (xCoordinate S * yCoordinate S)) (xCoordinate S))
    simpa only [map_mul] using
      (IsLocalization.Away.algebraMap_isUnit
        (S := Localization.Away (xCoordinate S * yCoordinate S))
        (xCoordinate S * yCoordinate S))

/-- The difference of the two canonical maps into the localization at `xy`. -/
noncomputable def localizationDifference (S : PuncturedAffinePlane.{u}) :
    Localization.Away (xCoordinate S) × Localization.Away (yCoordinate S) →+
      Localization.Away (xCoordinate S * yCoordinate S) :=
  (localizeXToXY S).toAddMonoidHom.comp (AddMonoidHom.fst _ _) -
    (localizeYToXY S).toAddMonoidHom.comp (AddMonoidHom.snd _ _)

section Helpers

private noncomputable def localizationToOpenSections (S : PuncturedAffinePlane.{u}) (f : S.R) :
    Localization.Away f →+*
      Γ(S.puncturedScheme, S.openImmersion ⁻¹ᵁ PrimeSpectrum.basicOpen f) :=
  (S.openImmersion.app (PrimeSpectrum.basicOpen f)).hom.comp
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f)))).toRingHom

private lemma localizationToOpenSections_sectionsToLocalization
    (S : PuncturedAffinePlane.{u}) (f : S.R)
    (hf : (PrimeSpectrum.basicOpen f : S.X.Opens) ≤ S.U) (s : Γ(S.puncturedScheme, ⊤)) :
    localizationToOpenSections S f (sectionsToLocalization S f hf s) =
      (S.puncturedScheme.presheaf.map (homOfLE le_top).op).hom s := by
  have hinst : IsIso (S.openImmersion.app (PrimeSpectrum.basicOpen f)) :=
    S.isIso_app_basicOpen hf
  have he : ∀ w, (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
        ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
          (Opposite.op (PrimeSpectrum.basicOpen f))))
      ((IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
        ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
          (Opposite.op (PrimeSpectrum.basicOpen f)))).symm w) = w :=
    fun w => AlgEquiv.apply_symm_apply _ w
  have hstep : localizationToOpenSections S f (sectionsToLocalization S f hf s) =
      (S.openImmersion.app (PrimeSpectrum.basicOpen f)).hom
        ((CategoryTheory.inv (S.openImmersion.app (PrimeSpectrum.basicOpen f))).hom
          ((S.puncturedScheme.presheaf.map (homOfLE le_top).op).hom s)) :=
    congrArg (S.openImmersion.app (PrimeSpectrum.basicOpen f)).hom (he _)
  exact hstep.trans (by simp)

private lemma localizationToOpenSections_injective (S : PuncturedAffinePlane.{u}) (f : S.R)
    (hf : (PrimeSpectrum.basicOpen f : S.X.Opens) ≤ S.U) :
    Function.Injective (localizationToOpenSections S f) := by
  have hbij : Function.Bijective (S.openImmersion.app (PrimeSpectrum.basicOpen f)).hom :=
    (ConcreteCategory.isIso_iff_bijective _).1 (S.isIso_app_basicOpen hf)
  let e : Localization.Away f ≃ₐ[S.R]
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f))) :=
    IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) _
  intro a b hab
  exact e.injective (hbij.1 hab)

private lemma basicOpen_mul_le_punctured (S : PuncturedAffinePlane.{u}) :
    (PrimeSpectrum.basicOpen (xCoordinate S * yCoordinate S) : S.X.Opens) ≤ S.U :=
  (PrimeSpectrum.basicOpen_mul_le_left _ _).trans (S.basicOpen_X_le_U 0)

private lemma xyOpen_le_xOpen (S : PuncturedAffinePlane.{u}) : S.xyOpen ≤ S.xOpen :=
  (PuncturedAffinePlane.xOpen_inf_yOpen S).ge.trans inf_le_left

private lemma xyOpen_le_yOpen (S : PuncturedAffinePlane.{u}) : S.xyOpen ≤ S.yOpen :=
  (PuncturedAffinePlane.xOpen_inf_yOpen S).ge.trans inf_le_right

/-- The localization at `x`, identified with the sections of the punctured plane on `xOpen`. -/
private noncomputable def xSections (S : PuncturedAffinePlane.{u}) :
    Localization.Away (xCoordinate S) →+* Γ(S.puncturedScheme, S.xOpen) :=
  localizationToOpenSections S (xCoordinate S)

/-- The localization at `y`, identified with the sections of the punctured plane on `yOpen`. -/
private noncomputable def ySections (S : PuncturedAffinePlane.{u}) :
    Localization.Away (yCoordinate S) →+* Γ(S.puncturedScheme, S.yOpen) :=
  localizationToOpenSections S (yCoordinate S)

/-- The localization at `xy`, identified with the sections of the punctured plane on `xyOpen`. -/
private noncomputable def xySections (S : PuncturedAffinePlane.{u}) :
    Localization.Away (xCoordinate S * yCoordinate S) →+* Γ(S.puncturedScheme, S.xyOpen) :=
  localizationToOpenSections S (xCoordinate S * yCoordinate S)

private lemma xSections_injective (S : PuncturedAffinePlane.{u}) :
    Function.Injective (xSections S) :=
  localizationToOpenSections_injective S (xCoordinate S) (S.basicOpen_X_le_U 0)

private lemma ySections_injective (S : PuncturedAffinePlane.{u}) :
    Function.Injective (ySections S) :=
  localizationToOpenSections_injective S (yCoordinate S) (S.basicOpen_X_le_U 1)

private lemma xySections_injective (S : PuncturedAffinePlane.{u}) :
    Function.Injective (xySections S) :=
  localizationToOpenSections_injective S (xCoordinate S * yCoordinate S)
    (basicOpen_mul_le_punctured S)

private lemma xSections_restrictToX (S : PuncturedAffinePlane.{u}) (s : Γ(S.puncturedScheme, ⊤)) :
    xSections S (restrictToX S s) =
      (S.puncturedScheme.presheaf.map (homOfLE (x := S.xOpen) le_top).op).hom s :=
  localizationToOpenSections_sectionsToLocalization S (xCoordinate S)
    (S.basicOpen_X_le_U 0) s

private lemma ySections_restrictToY (S : PuncturedAffinePlane.{u}) (s : Γ(S.puncturedScheme, ⊤)) :
    ySections S (restrictToY S s) =
      (S.puncturedScheme.presheaf.map (homOfLE (x := S.yOpen) le_top).op).hom s :=
  localizationToOpenSections_sectionsToLocalization S (yCoordinate S)
    (S.basicOpen_X_le_U 1) s

private lemma localizeXToXY_algebraMap (S : PuncturedAffinePlane.{u}) (r : S.R) :
    localizeXToXY S (algebraMap S.R (Localization.Away (xCoordinate S)) r) =
      algebraMap S.R (Localization.Away (xCoordinate S * yCoordinate S)) r := by
  simp [localizeXToXY]

private lemma localizeYToXY_algebraMap (S : PuncturedAffinePlane.{u}) (r : S.R) :
    localizeYToXY S (algebraMap S.R (Localization.Away (yCoordinate S)) r) =
      algebraMap S.R (Localization.Away (xCoordinate S * yCoordinate S)) r := by
  simp [localizeYToXY]

/-- A ring map between localizations compatible with `algebraMap` commutes with the identification
of localizations with sections of the punctured plane and the restriction of sections. -/
private lemma localizationToOpenSections_comp (S : PuncturedAffinePlane.{u}) {f h : S.R}
    (hle : (PrimeSpectrum.basicOpen h : S.X.Opens) ≤ PrimeSpectrum.basicOpen f)
    (g : Localization.Away f →+* Localization.Away h)
    (hg : ∀ r, g (algebraMap S.R (Localization.Away f) r) = algebraMap S.R (Localization.Away h) r)
    (a : Localization.Away f) :
    localizationToOpenSections S h (g a) =
      (S.puncturedScheme.presheaf.map (homOfLE (S.openImmersion.preimage_mono hle)).op).hom
        (localizationToOpenSections S f a) := by
  let i : Opposite.op (PrimeSpectrum.basicOpen f) ⟶ Opposite.op (PrimeSpectrum.basicOpen h) :=
    (homOfLE hle).op
  let iu : Opposite.op (S.openImmersion ⁻¹ᵁ PrimeSpectrum.basicOpen f) ⟶
      Opposite.op (S.openImmersion ⁻¹ᵁ PrimeSpectrum.basicOpen h) :=
    (homOfLE (S.openImmersion.preimage_mono hle)).op
  let e₁ : Localization.Away f ≃ₐ[S.R]
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f))) :=
    IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) _
  let e₂ : Localization.Away h ≃ₐ[S.R]
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen h))) :=
    IsLocalization.algEquiv (Submonoid.powers h) (Localization.Away h) _
  have hmap : (S.X.presheaf.map i).hom.comp e₁.toRingHom = e₂.toRingHom.comp g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    refine RingHom.ext fun r => ?_
    change (S.X.presheaf.map i).hom (e₁ (algebraMap S.R _ r)) = e₂ (g (algebraMap S.R _ r))
    rw [e₁.commutes, hg, e₂.commutes]
    exact congrArg (fun φ => CommRingCat.Hom.hom φ r)
      (StructureSheaf.algebraMap_self_map S.R _ _ i)
  have hcat : S.X.presheaf.map i ≫ S.openImmersion.app (PrimeSpectrum.basicOpen h) =
      S.openImmersion.app (PrimeSpectrum.basicOpen f) ≫ S.puncturedScheme.presheaf.map iu :=
    (S.openImmersion.naturality i).trans
      (congrArg (fun a => S.openImmersion.app (PrimeSpectrum.basicOpen f) ≫
        S.puncturedScheme.presheaf.map a) (Subsingleton.elim _ iu))
  exact ((DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hcat) (e₁ a)).trans
    (congrArg (S.openImmersion.app (PrimeSpectrum.basicOpen h)).hom
      (DFunLike.congr_fun hmap a))).symm

private lemma xySections_localizeXToXY (S : PuncturedAffinePlane.{u})
    (a : Localization.Away (xCoordinate S)) :
    xySections S (localizeXToXY S a) =
      (S.puncturedScheme.presheaf.map (homOfLE (xyOpen_le_xOpen S)).op).hom (xSections S a) :=
  localizationToOpenSections_comp S (PrimeSpectrum.basicOpen_mul_le_left _ _) _
    (localizeXToXY_algebraMap S) a

private lemma xySections_localizeYToXY (S : PuncturedAffinePlane.{u})
    (b : Localization.Away (yCoordinate S)) :
    xySections S (localizeYToXY S b) =
      (S.puncturedScheme.presheaf.map (homOfLE (xyOpen_le_yOpen S)).op).hom (ySections S b) :=
  localizationToOpenSections_comp S (PrimeSpectrum.basicOpen_mul_le_right _ _) _
    (localizeYToXY_algebraMap S) b


private lemma presheaf_map_map_apply {X : Scheme} {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (k : W ⟶ U) (s : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.map k.op).hom s := by
  simp only [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
  congr 1

private lemma restrict_top_xyOpen (S : PuncturedAffinePlane.{u}) {V : S.puncturedScheme.Opens}
    (h : S.xyOpen ≤ V) (s : Γ(S.puncturedScheme, ⊤)) :
    (S.puncturedScheme.presheaf.map (homOfLE h).op).hom
        ((S.puncturedScheme.presheaf.map (homOfLE (x := V) le_top).op).hom s) =
      (S.puncturedScheme.presheaf.map (homOfLE (x := S.xyOpen) le_top).op).hom s :=
  presheaf_map_map_apply _ _ _ s

end Helpers

/-- **Stacks Project, Tag 01IL, sections exact sequence.** Restriction of global
sections to the two standard affine opens is injective. -/
@[stacks 01IL "sections_exact_sequence"]
theorem restrictionPair_injective (S : PuncturedAffinePlane.{u}) :
    Function.Injective (restrictionPair S) := by
  intro s t hst
  change (restrictToX S s, restrictToY S s) = (restrictToX S t, restrictToY S t) at hst
  have hx : restrictToX S s = restrictToX S t := congrArg Prod.fst hst
  have hy : restrictToY S s = restrictToY S t := congrArg Prod.snd hst
  have hxR : (S.puncturedScheme.presheaf.map (homOfLE (x := S.xOpen) le_top).op).hom s =
      (S.puncturedScheme.presheaf.map (homOfLE (x := S.xOpen) le_top).op).hom t := by
    rw [← xSections_restrictToX, ← xSections_restrictToX, hx]
  have hyR : (S.puncturedScheme.presheaf.map (homOfLE (x := S.yOpen) le_top).op).hom s =
      (S.puncturedScheme.presheaf.map (homOfLE (x := S.yOpen) le_top).op).hom t := by
    rw [← ySections_restrictToY, ← ySections_restrictToY, hy]
  refine TopCat.Presheaf.IsSheaf.section_ext S.puncturedScheme.IsSheaf fun p hp => ?_
  rw [← PuncturedAffinePlane.xOpen_sup_yOpen S] at hp
  rcases TopologicalSpace.Opens.mem_sup.mp hp with hpX | hpY
  · exact ⟨S.xOpen, le_top, hpX, hxR⟩
  · exact ⟨S.yOpen, le_top, hpY, hyR⟩

section Helpers

private lemma localizationDifference_restrictionPair_zero
    (S : PuncturedAffinePlane.{u}) (s : Γ(S.puncturedScheme, ⊤)) :
    localizationDifference S (restrictionPair S s) = 0 := by
  show localizeXToXY S (restrictToX S s) - localizeYToXY S (restrictToY S s) = 0
  refine sub_eq_zero.mpr (xySections_injective S ?_)
  rw [xySections_localizeXToXY, xySections_localizeYToXY, xSections_restrictToX,
    ySections_restrictToY, restrict_top_xyOpen, restrict_top_xyOpen]

/-- A pair of localizations agreeing in the localization at `xy` comes from a global section
of the punctured plane. -/
private theorem exists_restrictionPair_eq_of_localizeXToXY_eq (S : PuncturedAffinePlane.{u})
    {a : Localization.Away (xCoordinate S)} {b : Localization.Away (yCoordinate S)}
    (hab : localizeXToXY S a = localizeYToXY S b) :
    ∃ s, restrictionPair S s = (a, b) := by
  set sx := xSections S a with hsxdef
  set sy := ySections S b with hsydef
  let iX : S.xyOpen ⟶ S.xOpen := homOfLE (xyOpen_le_xOpen S)
  let iY : S.xyOpen ⟶ S.yOpen := homOfLE (xyOpen_le_yOpen S)
  have hxy : (S.puncturedScheme.presheaf.map iX.op).hom sx =
      (S.puncturedScheme.presheaf.map iY.op).hom sy := by
    rw [hsxdef, hsydef, ← xySections_localizeXToXY, ← xySections_localizeYToXY, hab]
  let U : Bool → S.puncturedScheme.Opens := fun i => if i then S.yOpen else S.xOpen
  let sf : ∀ i, Γ(S.puncturedScheme, U i) := fun
    | false => sx
    | true => sy
  let eXY : S.xOpen ⊓ S.yOpen ⟶ S.xyOpen := eqToHom (PuncturedAffinePlane.xOpen_inf_yOpen S)
  let eYX : S.yOpen ⊓ S.xOpen ⟶ S.xyOpen :=
    eqToHom ((inf_comm _ _).trans (PuncturedAffinePlane.xOpen_inf_yOpen S))
  have hcompatXY : (S.puncturedScheme.presheaf.map
        (TopologicalSpace.Opens.infLELeft S.xOpen S.yOpen).op).hom sx =
      (S.puncturedScheme.presheaf.map
        (TopologicalSpace.Opens.infLERight S.xOpen S.yOpen).op).hom sy := by
    rw [← presheaf_map_map_apply iX eXY _ sx, ← presheaf_map_map_apply iY eXY _ sy, hxy]
  have hcompatYX : (S.puncturedScheme.presheaf.map
        (TopologicalSpace.Opens.infLELeft S.yOpen S.xOpen).op).hom sy =
      (S.puncturedScheme.presheaf.map
        (TopologicalSpace.Opens.infLERight S.yOpen S.xOpen).op).hom sx := by
    rw [← presheaf_map_map_apply iY eYX _ sy, ← presheaf_map_map_apply iX eYX _ sx, hxy]
  have hcompat : S.puncturedScheme.presheaf.IsCompatible U sf := by
    intro i j
    cases i <;> cases j
    · congr 1
    · simpa [U, sf] using hcompatXY
    · simpa [U, sf] using hcompatYX
    · congr 1
  have hcover : (⊤ : S.puncturedScheme.Opens) ≤ iSup U := by
    rw [iSup_bool_eq]
    simpa [U, sup_comm] using
      (le_of_eq (PuncturedAffinePlane.xOpen_sup_yOpen S).symm)
  obtain ⟨s, hs, -⟩ := S.puncturedScheme.sheaf.existsUnique_gluing'
    U (⊤ : S.puncturedScheme.Opens) (fun _ => homOfLE le_top) hcover sf hcompat
  have hsx : (S.puncturedScheme.presheaf.map
      (homOfLE (x := S.xOpen) le_top).op).hom s = sx := hs false
  have hsy : (S.puncturedScheme.presheaf.map
      (homOfLE (x := S.yOpen) le_top).op).hom s = sy := hs true
  refine ⟨s, ?_⟩
  show (restrictToX S s, restrictToY S s) = (a, b)
  exact Prod.ext
    (xSections_injective S ((xSections_restrictToX S s).trans (hsx.trans hsxdef.symm)))
    (ySections_injective S ((ySections_restrictToY S s).trans (hsy.trans hsydef.symm)))

end Helpers

/-- **Stacks Project, Tag 01IL, sections exact sequence.** The image of global
sections in the product of the two localizations is the kernel of the
difference of restrictions to the intersection. -/
@[stacks 01IL "sections_exact_sequence"]
theorem restrictionPair_exact (S : PuncturedAffinePlane.{u}) :
    Function.Exact (restrictionPair S) (localizationDifference S) := by
  intro z
  refine ⟨fun hz => ?_, ?_⟩
  · obtain ⟨a, b⟩ := z
    change localizeXToXY S a - localizeYToXY S b = 0 at hz
    exact exists_restrictionPair_eq_of_localizeXToXY_eq S (sub_eq_zero.mp hz)
  · rintro ⟨s, rfl⟩
    exact localizationDifference_restrictionPair_zero S s

section Helpers

private lemma exists_eq_mul_pow_of_mul_pow_eq {R : Type*} [CommRing R] [IsDomain R]
    {x y p q : R} (hx : Prime x) (hxy : ¬ x ∣ y) {m n : ℕ} (h : p * y ^ m = q * x ^ n) :
    ∃ c, p = c * x ^ n ∧ q = c * y ^ m := by
  obtain ⟨c, hc⟩ := hx.pow_dvd_of_dvd_mul_right (a := p) (b := y ^ m) n
    (fun h' => hxy (hx.dvd_of_dvd_pow h')) ⟨q, by rw [h]; ring⟩
  refine ⟨c, hc.trans (mul_comm _ _), mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
  rw [← mul_assoc, ← hc, h, mul_comm]

private lemma algebraMap_eq_of_mul_pow_eq {R L : Type*} [CommRing R] [CommRing L] [Algebra R L]
    (x : R) [IsLocalization.Away x L] {a : L} {n : ℕ} {p c : R}
    (ha : a * algebraMap R L (x ^ n) = algebraMap R L p) (hp : p = c * x ^ n) :
    algebraMap R L c = a := by
  refine (IsLocalization.Away.algebraMap_pow_isUnit x n).mul_left_inj.mp ?_
  rw [← map_pow, ← map_mul, ← hp, ← ha]

private lemma localization_intersection (S : PuncturedAffinePlane.{u})
    {a : Localization.Away (xCoordinate S)}
    {b : Localization.Away (yCoordinate S)}
    (hab : localizeXToXY S a = localizeYToXY S b) :
    ∃ r : S.R,
      algebraMap S.R (Localization.Away (xCoordinate S)) r = a ∧
      algebraMap S.R (Localization.Away (yCoordinate S)) r = b := by
  let x : S.R := xCoordinate S
  let y : S.R := yCoordinate S
  let Lx := Localization.Away x
  let Ly := Localization.Away y
  let Lxy := Localization.Away (x * y)
  have hxprime : Prime x := by
    dsimp [x, xCoordinate]
    exact MvPolynomial.X_prime
  have hx0 : x ≠ 0 := hxprime.ne_zero
  have hy0 : y ≠ 0 := by
    dsimp [y, yCoordinate]
    exact MvPolynomial.X_ne_zero 1
  have hxy : ¬ x ∣ y := by
    intro h
    have h01 : (0 : Fin 2) = 1 := by
      simpa [x, y, xCoordinate, yCoordinate] using (MvPolynomial.X_dvd_X.mp h)
    exact Fin.zero_ne_one h01
  let ca := IsLocalization.Away.sec x a
  let cb := IsLocalization.Away.sec y b
  have ha : a * algebraMap S.R Lx (x ^ ca.2) = algebraMap S.R Lx ca.1 := by
    simpa [ca, x, Lx] using IsLocalization.Away.sec_spec x a
  have hb : b * algebraMap S.R Ly (y ^ cb.2) = algebraMap S.R Ly cb.1 := by
    simpa [cb, y, Ly] using IsLocalization.Away.sec_spec y b
  have ha' := congrArg (localizeXToXY S) ha
  have hb' := congrArg (localizeYToXY S) hb
  rw [map_mul, localizeXToXY_algebraMap, localizeXToXY_algebraMap] at ha'
  rw [map_mul, localizeYToXY_algebraMap, localizeYToXY_algebraMap] at hb'
  have hcross : algebraMap S.R Lxy (ca.1 * y ^ cb.2) =
      algebraMap S.R Lxy (cb.1 * x ^ ca.2) := by
    calc
      algebraMap S.R Lxy (ca.1 * y ^ cb.2) =
          algebraMap S.R Lxy ca.1 * algebraMap S.R Lxy (y ^ cb.2) := by rw [map_mul]
      _ = (localizeXToXY S a * algebraMap S.R Lxy (x ^ ca.2)) *
          algebraMap S.R Lxy (y ^ cb.2) := by rw [← ha']
      _ = (localizeYToXY S b * algebraMap S.R Lxy (y ^ cb.2)) *
          algebraMap S.R Lxy (x ^ ca.2) := by rw [hab]; ring
      _ = algebraMap S.R Lxy (cb.1 * x ^ ca.2) := by rw [hb', map_mul]
  have hcross' : ca.1 * y ^ cb.2 = cb.1 * x ^ ca.2 :=
    IsLocalization.injective Lxy
      (powers_le_nonZeroDivisors_of_noZeroDivisors (mul_ne_zero hx0 hy0)) hcross
  obtain ⟨c, hca, hcb⟩ := exists_eq_mul_pow_of_mul_pow_eq hxprime hxy hcross'
  exact ⟨c, algebraMap_eq_of_mul_pow_eq x ha hca, algebraMap_eq_of_mul_pow_eq y hb hcb⟩

private lemma restrictToCoordinate_coordinateMap (S : PuncturedAffinePlane.{u}) (j : Fin 2) :
    (sectionsToLocalization S (MvPolynomial.X j) (S.basicOpen_X_le_U j)).comp
      ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.openImmersion.appTop).hom =
      algebraMap S.R (Localization.Away ((MvPolynomial.X j : S.R))) := by
  let V : S.X.Opens := PrimeSpectrum.basicOpen ((MvPolynomial.X j : S.R))
  have hinst : IsIso (S.openImmersion.app V) :=
    S.isIso_app_basicOpen (S.basicOpen_X_le_U j)
  let i : Opposite.op ⊤ ⟶ Opposite.op V := (homOfLE (show V ≤ ⊤ from le_top)).op
  have hsrc : S.puncturedScheme.presheaf.map (homOfLE le_top).op =
      S.puncturedScheme.presheaf.map
        (((TopologicalSpace.Opens.map S.openImmersion.base).map i.unop).op) := by
    congr 1
  have hnat := S.openImmersion.naturality i
  rw [← hsrc] at hnat
  have hnat' : S.X.presheaf.map i ≫ S.openImmersion.app V =
      S.openImmersion.appTop ≫ S.puncturedScheme.presheaf.map (homOfLE le_top).op := hnat
  have hcancel : S.openImmersion.appTop ≫
      S.puncturedScheme.presheaf.map (homOfLE le_top).op ≫
      CategoryTheory.inv (S.openImmersion.app V) = S.X.presheaf.map i := by
    rw [← Category.assoc, ← hnat', Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hcomp :
      (CategoryTheory.inv (S.openImmersion.app V)).hom.comp
        ((S.puncturedScheme.presheaf.map (homOfLE le_top).op).hom.comp
          ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.openImmersion.appTop).hom) =
      (S.X.presheaf.map i).hom.comp (Scheme.ΓSpecIso (.of S.R)).inv.hom :=
    congrArg (fun φ => φ.comp (Scheme.ΓSpecIso (.of S.R)).inv.hom)
      (congrArg CommRingCat.Hom.hom hcancel)
  change
    (IsLocalization.algEquiv (Submonoid.powers ((MvPolynomial.X j : S.R)))
      (Localization.Away ((MvPolynomial.X j : S.R)))
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen ((MvPolynomial.X j : S.R)))))).symm.toRingHom.comp
      ((CategoryTheory.inv (S.openImmersion.app V)).hom.comp
        ((S.puncturedScheme.presheaf.map (homOfLE le_top).op).hom.comp
          ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.openImmersion.appTop).hom)) = _
  rw [hcomp, ← CommRingCat.hom_comp]
  let _ : Algebra (CommRingCat.of S.R) Γ(Spec (CommRingCat.of S.R), V) :=
    inferInstanceAs (Algebra (CommRingCat.of S.R)
      ((Spec.structureSheaf (CommRingCat.of S.R)).presheaf.obj (Opposite.op V)))
  show (IsLocalization.algEquiv (Submonoid.powers ((MvPolynomial.X j : S.R)))
      (Localization.Away ((MvPolynomial.X j : S.R)))
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen ((MvPolynomial.X j : S.R)))))).symm.toRingHom.comp
      (algebraMap (CommRingCat.of S.R) Γ(Spec (CommRingCat.of S.R), V)) =
      algebraMap S.R (Localization.Away ((MvPolynomial.X j : S.R)))
  exact RingHom.ext fun r =>
    (IsLocalization.algEquiv (Submonoid.powers ((MvPolynomial.X j : S.R)))
      (Localization.Away ((MvPolynomial.X j : S.R)))
      ((Spec.structureSheaf (CommRingCat.of S.R)).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen ((MvPolynomial.X j : S.R)))))).symm.commutes r

end Helpers

/-- The canonical homomorphism from the coordinate ring of the affine plane to the global
sections of the punctured affine plane is an isomorphism. -/
@[stacks 01IL "punctured_plane_global_sections"]
theorem isIso_coordinateRingToGlobalSections (S : PuncturedAffinePlane.{u}) :
    IsIso ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.openImmersion.appTop) := by
  let φ := ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.openImmersion.appTop).hom
  have hX : (restrictToX S).comp φ =
      algebraMap S.R (Localization.Away (xCoordinate S)) :=
    restrictToCoordinate_coordinateMap S 0
  have hY : (restrictToY S).comp φ =
      algebraMap S.R (Localization.Away (yCoordinate S)) :=
    restrictToCoordinate_coordinateMap S 1
  have hinjX : Function.Injective (algebraMap S.R (Localization.Away (xCoordinate S))) :=
    IsLocalization.injective (Localization.Away (xCoordinate S))
      (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero (0 : Fin 2)))
  refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨fun r s hrs => ?_, fun t => ?_⟩
  · apply hinjX
    simpa only [RingHom.comp_apply, ← hX] using congrArg (restrictToX S) hrs
  · have heq : localizeXToXY S (restrictToX S t) = localizeYToXY S (restrictToY S t) := by
      apply sub_eq_zero.mp
      simpa [localizationDifference, restrictionPair] using
        (restrictionPair_exact S (restrictionPair S t)).mpr ⟨t, rfl⟩
    obtain ⟨r, hrx, hry⟩ := localization_intersection S heq
    refine ⟨r, ?_⟩
    apply restrictionPair_injective S
    apply Prod.ext
    · show restrictToX S (φ r) = restrictToX S t
      rw [← RingHom.comp_apply, hX, hrx]
    · show restrictToY S (φ r) = restrictToY S t
      rw [← RingHom.comp_apply, hY, hry]

end AlgebraicGeometry

end
