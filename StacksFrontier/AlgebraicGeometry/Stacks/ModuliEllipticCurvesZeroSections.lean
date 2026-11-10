module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartPullbackCotensorator
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTripleClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTriplePullbackEquiv
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceGeneratingSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesZeroDivisor
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassMonomials

/-!
# Sections of the powers of `O(0)` on a pointed family, and their restriction

For a pointed family `E` over `S`, with zero divisor `0`, we consider the invertible sheaf `O(0)`
on the total space and its canonical section in degree one. For a morphism `g : T ⟶ S`, a section
of `O(0)^{⊗ n}` restricts to a section of the corresponding power of `O(0)` on the pulled-back
family `E ×_{S,g} T`. Restriction is multiplicative, carries the canonical section to the canonical
section, and hence carries the Weierstrass monomials to the Weierstrass monomials.

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.zeroSheaf`: the invertible sheaf `O(0)`.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.zeroSection`: the canonical section of
  `O(0)` in degree one.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.restrictSection`: the restriction of a
  section of a power of `O(0)` along base change.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.restrictSection_mulSections`: restriction
  is multiplicative.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.restrictSection_zeroSection`: restriction
  carries the canonical section to the canonical section.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.restrictSection_weierstrassMonomials`:
  restriction carries the Weierstrass monomials to the Weierstrass monomials.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open Stacks.Divisors
open Stacks.TensorPowers (natTensorPow)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (mulSections)
open Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections (twistOneSection)

universe u

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

namespace Stacks.AlgebraicGeometry.ProjChartRatioPullback

variable {Y Y' : Scheme.{u}} (j : Y' ⟶ Y)

/-- Pulling back a section is natural in the module. -/
theorem pullbackSectionHom_naturality {M N : Y.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    pullbackSectionHom j N ⊤ ⊤ (top_le_preimage_top j) (Scheme.Modules.Hom.app φ ⊤ x) =
      Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map φ) ⊤
        (pullbackSectionHom j M ⊤ ⊤ (top_le_preimage_top j) x) := by
  have hu := (Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality φ
  have hu' := congrArg (fun ψ => Scheme.Modules.Hom.app ψ ⊤ x) hu
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, ConcreteCategory.comp_apply] at hu'
  unfold pullbackSectionHom
  change ((Scheme.Modules.pullback j).obj N).presheaf.map (homOfLE (top_le_preimage_top j)).op
      (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N) ⊤
        (Scheme.Modules.Hom.app φ ⊤ x)) =
    Scheme.Modules.Hom.app ((Scheme.Modules.pullback j).map φ) ⊤
      (((Scheme.Modules.pullback j).obj M).presheaf.map (homOfLE (top_le_preimage_top j)).op
        (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) ⊤ x))
  rw [hu']
  exact (ConcreteCategory.congr_hom
    (((Scheme.Modules.pullback j).map φ).mapPresheaf.naturality
      (homOfLE (top_le_preimage_top j)).op)
    (Scheme.Modules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app M) ⊤
      x)).symm

variable (L : Y.Modules) [Stacks.Ample.IsInvertibleModule Y L]

/-- **Pulling back a section of `L` and twisting it into degree one commute.** -/
theorem pullSection_twistOneSection (x : Γ(L, ⊤)) :
    pullSection j L 1 (twistOneSection L x) =
      twistOneSection ((Scheme.Modules.pullback j).obj L)
        (pullbackSectionHom j L ⊤ ⊤ (top_le_preimage_top j) x) := by
  have h0 := Stacks.AlgebraicGeometry.ProjChartSectionPullback.pullbackNatTensorPowIso_inv_zero j L
  have h1 :=
    Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullbackNatTensorPowIso_inv_succ j L 0
  have hl := Stacks.TensorSheafSpellingIso.pullbackCotensorator_leftUnitor Y j L
  have key : (Scheme.Modules.pullback j).map (MorphismToProjUniversal.unitorPow L).hom =
      (pullbackNatTensorPowIso j L 1).inv ≫
        (MorphismToProjUniversal.unitorPow ((Scheme.Modules.pullback j).obj L)).hom := by
    rw [h1]
    exact (hl.trans (congrArg (fun φ : (Scheme.Modules.pullback j).obj (natTensorPow L 0) ⟶
        natTensorPow ((Scheme.Modules.pullback j).obj L) 0 =>
      ProjChartPullbackCotensorator.pullbackCotensorator j (natTensorPow L 0) L ≫
        (φ ▷ (Scheme.Modules.pullback j).obj L) ≫
          (MorphismToProjUniversal.unitorPow ((Scheme.Modules.pullback j).obj L)).hom)
            h0).symm).trans (Category.assoc _ _ _).symm
  have key' : (Scheme.Modules.pullback j).map (MorphismToProjUniversal.unitorPow L).inv ≫
      (pullbackNatTensorPowIso j L 1).inv =
        (MorphismToProjUniversal.unitorPow ((Scheme.Modules.pullback j).obj L)).inv := by
    rw [← cancel_mono (MorphismToProjUniversal.unitorPow ((Scheme.Modules.pullback j).obj L)).hom,
      Category.assoc, ← key, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Iso.inv_hom_id]
  change Scheme.Modules.Hom.app (pullbackNatTensorPowIso j L 1).inv ⊤
      (pullbackSectionHom j (natTensorPow L 1) ⊤ ⊤ (top_le_preimage_top j)
        (Scheme.Modules.Hom.app (MorphismToProjUniversal.unitorPow L).inv ⊤ x)) =
    Scheme.Modules.Hom.app
      (MorphismToProjUniversal.unitorPow ((Scheme.Modules.pullback j).obj L)).inv ⊤
      (pullbackSectionHom j L ⊤ ⊤ (top_le_preimage_top j) x)
  rw [pullbackSectionHom_naturality, ← key']
  rfl

/-- The degree-one twist is natural for isomorphisms of the module. -/
theorem natTensorPowCongr_one_twistOneSection {L L' : Y.Modules} (e : L ≅ L') (z : Γ(L, ⊤)) :
    (Stacks.AmplePullbackPart1.natTensorPowCongr e 1).hom.app ⊤ (twistOneSection L z) =
      twistOneSection L' (e.hom.app ⊤ z) := by
  have h : (MorphismToProjUniversal.unitorPow L).inv ≫
      (Stacks.AmplePullbackPart1.natTensorPowCongr e 1).hom =
        e.hom ≫ (MorphismToProjUniversal.unitorPow L').inv := by
    change (λ_ L).inv ≫ (Iso.refl (𝟙_ Y.Modules) ⊗ᵢ e).hom = e.hom ≫ (λ_ L').inv
    rw [tensorIso_hom, Iso.refl_hom, id_tensorHom, leftUnitor_inv_naturality]
  exact congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ z) h

end Stacks.AlgebraicGeometry.ProjChartRatioPullback

/-! ### The powers of `O(0)` on a pointed family, and their restriction along base change -/

namespace AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

open Stacks.AmplePullbackPart1 (natTensorPowCongr)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback

variable {S T : Scheme.{u}} (E : PointedFamily S) [IsSeparated E.map]
  [SmoothOfRelativeDimension 1 E.map]

/-- The invertible sheaf `O(0)` of the zero divisor. -/
abbrev zeroSheaf : E.total.Modules :=
  invertibleSheaf' E.zeroDivisor

/-- The sheaf `O(0)` is invertible. -/
instance isInvertibleModule_zeroSheaf : Stacks.Ample.IsInvertibleModule E.total E.zeroSheaf :=
  invertibleSheaf_isInvertible E.zeroDivisor

/-- The canonical section of `O(0)`, in degree one of its section ring. -/
def zeroSection : Γ(natTensorPow E.zeroSheaf 1, ⊤) :=
  twistOneSection E.zeroSheaf ((canonicalSection' E.zeroDivisor).val (op ⊤))

/-- The identification of the pullback of `O(0)` to `E ×_{S,g} T` with `O(0)` of the pulled-back
family, carrying the canonical section to the canonical section. -/
def zeroSheafPullbackIso (g : T ⟶ S) :
    (Scheme.Modules.pullback (Limits.pullback.fst E.map g)).obj E.zeroSheaf ≅
      (E.pullback g).zeroSheaf :=
  Classical.choose (E.exists_pullback_zeroDivisor_invertibleSheaf_iso g)

/-- The isomorphism `zeroSheafPullbackIso` carries the pullback of the canonical section of `O(0)`
to the canonical section of `O(0)` of the pulled-back family. -/
theorem zeroSheafPullbackIso_canonicalSection (g : T ⟶ S) :
    Scheme.Modules.Hom.app (E.zeroSheafPullbackIso g).hom ⊤
        (pullbackCanonicalSection _ E.zeroDivisor) =
      (canonicalSection' (E.pullback g).zeroDivisor).val (op ⊤) :=
  Classical.choose_spec (E.exists_pullback_zeroDivisor_invertibleSheaf_iso g)

/-- **The restriction of a section of a power of `O(0)` along base change** `E ×_{S,g} T ⟶ E`. -/
def restrictSection (g : T ⟶ S) (n : ℕ) (x : Γ(natTensorPow E.zeroSheaf n, ⊤)) :
    Γ(natTensorPow (E.pullback g).zeroSheaf n, ⊤) :=
  (natTensorPowCongr (E.zeroSheafPullbackIso g) n).hom.app ⊤
    (pullSection (Limits.pullback.fst E.map g) E.zeroSheaf n x)

/-- **Restriction is multiplicative.** -/
theorem restrictSection_mulSections (g : T ⟶ S) {n m : ℕ} (x : Γ(natTensorPow E.zeroSheaf n, ⊤))
    (y : Γ(natTensorPow E.zeroSheaf m, ⊤)) :
    E.restrictSection g (n + m) (mulSections E.zeroSheaf x y) =
      mulSections (E.pullback g).zeroSheaf (E.restrictSection g n x)
        (E.restrictSection g m y) := by
  rw [restrictSection,
    Stacks.AlgebraicGeometry.ProjChartPullbackCotensorator.pullSection_mulSections,
    Stacks.AlgebraicGeometry.ProjTripleClassifying.mulSections_natTensorPowCongr]
  rfl

/-- **Restriction carries the canonical section to the canonical section.** -/
theorem restrictSection_zeroSection (g : T ⟶ S) :
    E.restrictSection g 1 E.zeroSection = (E.pullback g).zeroSection := by
  unfold restrictSection zeroSection
  refine (congrArg (fun z => (natTensorPowCongr (E.zeroSheafPullbackIso g) 1).hom.app ⊤ z)
    (pullSection_twistOneSection _ _ _)).trans ?_
  refine (natTensorPowCongr_one_twistOneSection _ _).trans ?_
  congr 1
  exact E.zeroSheafPullbackIso_canonicalSection g

/-- Restriction commutes with squaring a section of degree one. -/
theorem restrictSection_sq (g : T ⟶ S) (a : Γ(natTensorPow E.zeroSheaf 1, ⊤)) :
    E.restrictSection g 2 (sq E.zeroSheaf a) =
      sq (E.pullback g).zeroSheaf (E.restrictSection g 1 a) :=
  E.restrictSection_mulSections g a a

/-- Restriction commutes with cubing a section of degree one. -/
theorem restrictSection_cube (g : T ⟶ S) (a : Γ(natTensorPow E.zeroSheaf 1, ⊤)) :
    E.restrictSection g 3 (cube E.zeroSheaf a) =
      cube (E.pullback g).zeroSheaf (E.restrictSection g 1 a) :=
  (E.restrictSection_mulSections g (sq E.zeroSheaf a) a).trans
    (congrArg (fun z => mulSections _ z _) (E.restrictSection_sq g a))

/-- **Restriction carries the Weierstrass monomials to the Weierstrass monomials.** -/
theorem restrictSection_weierstrassMonomials (g : T ⟶ S) (x : Γ(natTensorPow E.zeroSheaf 2, ⊤))
    (y : Γ(natTensorPow E.zeroSheaf 3, ⊤)) (i : Fin 6) :
    E.restrictSection g 6 (weierstrassMonomials E.zeroSheaf E.zeroSection x y i) =
      weierstrassMonomials (E.pullback g).zeroSheaf (E.pullback g).zeroSection
        (E.restrictSection g 2 x) (E.restrictSection g 3 y) i := by
  have hs := E.restrictSection_zeroSection g
  have hc := E.restrictSection_cube g E.zeroSection
  have hq := E.restrictSection_sq g E.zeroSection
  rw [hs] at hc hq
  have h33 := E.restrictSection_mulSections g (n := 3) (m := 3)
  fin_cases i
  · exact (h33 _ _).trans (by rw [hc]; rfl)
  · refine (E.restrictSection_mulSections g (n := 4) (m := 2) _ _).trans ?_
    change mulSections _ (E.restrictSection g (3 + 1) (mulSections _ _ _)) _ = _
    rw [E.restrictSection_mulSections, hc, hs]
    rfl
  · exact (h33 _ _).trans (by rw [hc]; rfl)
  · refine (E.restrictSection_mulSections g (n := 2) (m := 4) _ _).trans ?_
    change mulSections _ _ (E.restrictSection g (2 + 2) (mulSections _ _ _)) = _
    rw [E.restrictSection_mulSections, hq]
    rfl
  · refine (h33 _ _).trans ?_
    change mulSections _ (E.restrictSection g (1 + 2) (mulSections _ _ _)) _ = _
    rw [E.restrictSection_mulSections, hs]
    rfl
  · refine (E.restrictSection_mulSections g (n := 4) (m := 2) _ _).trans ?_
    change mulSections _ (E.restrictSection g (2 + 2) (mulSections _ _ _)) _ = _
    rw [E.restrictSection_mulSections]
    rfl

/-- Restriction commutes with squaring a section of degree three. -/
theorem restrictSection_ySq (g : T ⟶ S) (y : Γ(natTensorPow E.zeroSheaf 3, ⊤)) :
    E.restrictSection g 6 (ySq E.zeroSheaf y) =
      ySq (E.pullback g).zeroSheaf (E.restrictSection g 3 y) :=
  E.restrictSection_mulSections g y y

end AlgebraicGeometry.ModuliEllipticCurves.PointedFamily

end
