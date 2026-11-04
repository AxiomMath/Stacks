module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoGlue
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaChartDatum
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistChartBridge.TwistQuadrupleChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedPullback
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTransport

/-!
# Clause (2) of Stacks Tag 01O9

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : X ⟶ S` a morphism, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_n ℒ^{⊗ n}` a homomorphism of graded algebras. Clause (2)
of [Stacks, Tag 01O9] says: for `k ≥ 1` and an open `W ⊆ X` on which `ψ_k : f^*𝒜_k|_W ⟶ ℒ^{⊗ k}|_W`
is surjective, the restriction of `r_{ℒ,ψ}` to `W` is the morphism `W ⟶ Proj_S(𝒜)` which the
construction of the relative homogeneous spectrum attaches to
`(k, f|_W, ℒ^{⊗ k}|_W, ψ|_{𝒜^{(k)}})`. In particular `W ⊆ U(ψ)`.

The proof works over one affine open `V` of the base at a time, on the part `W ∩ f^{-1}(V)` of `W`.
There the restriction of `r_{ℒ,ψ}` is the morphism of [Stacks, Tag 01NK] for the datum `ψ` induces
over `𝒜(V)`, pulled back to `W ∩ f^{-1}(V)`, and the morphism of the relative homogeneous spectrum
is the classifying morphism of [Stacks, Tag 01N8] of the Veronese family of the quadruple over the
chart of `V`. Both data are, degree by degree, the pullback of the same value of `ψ` along
`W ∩ f^{-1}(V) ⟶ X`, read through two comparisons of tensor powers, so
`…RelativeProjInvertibleMorphism.coveringOpen_ι_toProj_classifyingHom` identifies the two morphisms
and `…RelativeProjInvertibleMorphism.coveringOpen_eq_top_of_family` shows that the first datum
generates everywhere. `…RelativeProjInvertibleMorphism.clauseTwo_of_parts` glues the parts.

## Main results

* `…RelativeProjInvertibleMorphism.partFamily_toFun`: over an affine open `V` of the base, the
  two data are carried to each other by `…RelativeProjInvertibleMorphism.partFamily`.
* `…RelativeProjInvertibleMorphism.partDatum_coveringOpen_and_glued`: clause (2) on the part of
  `W` over `V`.
* `…RelativeProjInvertibleMorphism.clauseTwo`: **clause (2) of [Stacks, Tag 01O9].**

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01O0](https://stacks.math.columbia.edu/tag/01O0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.MorphismsIntoProj (toProj)
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection pullbackNatTensorPowIso)
open Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul (restrictPowSection pullPowSection)
open Stacks.TensorPowers (natTensorPow)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

section Restrict

variable {T : Scheme.{u}} (L : T.Modules) [Stacks.Ample.IsInvertibleModule T L]
  (U : T.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme)

/-- The comparison `(j^*(L|_U))^{⊗ m} ≅ (j ≫ ι_U)^*(L^{⊗ m})`, `L^{⊗ m}` the power of
[Stacks, Tag 01CU]. -/
def restrictPullIso (m : ℕ) :
    (natTensorPow ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback U.ι).obj L)) m :
        Y.Modules) ≅
      (Scheme.Modules.pullback (j ≫ U.ι)).obj
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (m : ℤ)) :=
  pullbackNatTensorPowIso j ((Scheme.Modules.pullback U.ι).obj L) m ≪≫
    (Scheme.Modules.pullback j).mapIso
      (powCompare ((Scheme.Modules.pullback U.ι).obj L) m ≪≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L (m : ℤ)).symm) ≪≫
    (Scheme.Modules.pullbackComp j U.ι).app _

/-- Reading a section through `I.hom`, then `e.inv`, then `e.hom ≫ I.inv`, returns the section. -/
private theorem comp_inv_app_inv_app_hom_app {Z : Scheme.{u}} {P Q R : Z.Modules} (e : P ≅ Q)
    (I : R ≅ Q) (U : (Opens Z.toRingedSpace.carrier)ᵒᵖ) (z : R.val.obj U) :
    (e.hom ≫ I.inv).val.app U (e.inv.val.app U (I.hom.val.app U z)) = z := by
  change (I.hom ≫ e.inv ≫ e.hom ≫ I.inv).val.app U z = z
  simp
  rfl

/-- **A section over `U`, read on `U` and pulled back along `j`, is the pullback of the section
along `j ≫ ι_U`**, through `restrictPullIso`. -/
theorem restrictPullIso_pullSection (m : ℕ) (y : Γ(natTensorPow L m, U))
    (h : (⊤ : Y.Opens) ≤ (j ≫ U.ι) ⁻¹ᵁ U) :
    (restrictPullIso L U j m).hom.app ⊤
        (pullSection j ((Scheme.Modules.pullback U.ι).obj L) m (restrictPowSection L U m y))
      = Scheme.Modules.pullbackSection (j ≫ U.ι)
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (m : ℤ)) U ⊤ h
          ((powCompare L m).hom.app U y) := by
  have hι : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U :=
    Stacks.NonvanishingLocusRestrict.top_le_ι_preimage_self U
  have hj : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ (⊤ : U.toScheme.Opens) := fun _ _ => trivial
  set F := Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (m : ℤ)
  set w := (powCompare L m).hom.app U y
  -- the restricted section, before the conversion into the iterated power
  have h3 : ((powCompare ((Scheme.Modules.pullback U.ι).obj L) m).hom ≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L (m : ℤ)).inv).app ⊤
        (restrictPowSection L U m y)
      = Scheme.Modules.pullbackSection U.ι F U ⊤ hι w := by
    have n1 := PresheafOfModules.naturality_apply
      ((powCompare ((Scheme.Modules.pullback U.ι).obj L) m).hom ≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L (m : ℤ)).inv).val
      (homOfLE hι).op (pullPowSection U.ι L m U y)
    refine n1.trans ?_
    have c3 := comp_inv_app_inv_app_hom_app
      (powCompare ((Scheme.Modules.pullback U.ι).obj L) m)
      (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L (m : ℤ))
      (op (U.ι ⁻¹ᵁ U)) (pullbackUnit (ringedSpaceHom U.ι) F (op U) w)
    refine (congrArg (fun z => (((Scheme.Modules.pullback U.ι).obj F).val.map (homOfLE hι).op) z)
      c3).trans ?_
    rfl
  have h2 := Scheme.Modules.pullbackSection_naturality j
    ((powCompare ((Scheme.Modules.pullback U.ι).obj L) m).hom ≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L (m : ℤ)).inv)
    ⊤ ⊤ hj (restrictPowSection L U m y)
  have h5 := Scheme.Modules.pullbackSection_comp j U.ι F U ⊤ ⊤ hι hj h w
  have h1 := Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
    (pullbackNatTensorPowIso j ((Scheme.Modules.pullback U.ι).obj L) m) ⊤
    (Scheme.Modules.pullbackSection j _ ⊤ ⊤ hj (restrictPowSection L U m y))
  refine Eq.trans ?_ h5
  show ((Scheme.Modules.pullbackComp j U.ι).hom.app F).val.app (op ⊤)
      (((Scheme.Modules.pullback j).map
        ((powCompare ((Scheme.Modules.pullback U.ι).obj L) m).hom ≫
          (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L
            (m : ℤ)).inv)).val.app
        (op ⊤)
        ((pullbackNatTensorPowIso j ((Scheme.Modules.pullback U.ι).obj L) m).hom.app ⊤
          ((pullbackNatTensorPowIso j ((Scheme.Modules.pullback U.ι).obj L) m).inv.app ⊤
            (Scheme.Modules.pullbackSection j _ ⊤ ⊤ hj (restrictPowSection L U m y))))) = _
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp j U.ι).hom.app F).val.app (op ⊤)
      (((Scheme.Modules.pullback j).map
        ((powCompare ((Scheme.Modules.pullback U.ι).obj L) m).hom ≫
          (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom U.ι) L
            (m : ℤ)).inv)).val.app
        (op ⊤) z)) h1).trans ?_
  refine (congrArg (fun z => ((Scheme.Modules.pullbackComp j U.ι).hom.app F).val.app (op ⊤) z)
    h2).trans ?_
  exact congrArg (fun z => ((Scheme.Modules.pullbackComp j U.ι).hom.app F).val.app (op ⊤)
    (Scheme.Modules.pullbackSection j _ ⊤ ⊤ hj z)) h3

end Restrict

section ChartValue

open Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge (restrictₛₗ_three_eq_map)

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) {Z : Scheme.{u}} (g : Z ⟶ S) {k : ℕ}
  {M : SheafOfModules.{u} (structureRingSheaf Z.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf (isSheafStruct Z) M]
  (χ : Twisting g (situationAlgebra A) (k : ℤ) M) (V : S.Opens)
  (gV : (g ⁻¹ᵁ V).toScheme ⟶ V.toScheme) (hgV : (g ⁻¹ᵁ V).ι ≫ g = gV ≫ V.ι)

/-- **The chart-wise Veronese family of the restriction of a twisting to the preimage of an open
`V` of the base, computed**: on a homogeneous section of `A|_V` which is the restriction of one
of `𝒜(V)`, it is the value of the twisting on that section, pulled back to the preimage. -/
theorem veroneseSections_chartTwisting_restrict (n : ℕ)
    (x : (A.restrict V.ι).grading (⊤ : V.toScheme.Opens) (n * k))
    (yV : A.sectionPieces V (n * k))
    (hx : (x : (A.restrict V.ι).sectionRing (⊤ : V.toScheme.Opens)) (n * k) =
      A.resPiece (V.ι_image_top).le (n * k) yV)
    (hW : (⊤ : (g ⁻¹ᵁ V).toScheme.Opens) ≤ (g ⁻¹ᵁ V).ι ⁻¹ᵁ (g ⁻¹ᵁ V)) :
    letI : Stacks.Ample.IsInvertibleModule (g ⁻¹ᵁ V).toScheme
        ((pullbackFunctor (ringedSpaceHom (g ⁻¹ᵁ V).ι)).obj M) :=
      Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
    (veroneseSections (chartTwisting A V gV
        (Twisting.congrBase hgV (χ.pullback (g ⁻¹ᵁ V).ι)))).toFun n x =
      (powCompare ((pullbackFunctor (ringedSpaceHom (g ⁻¹ᵁ V).ι)).obj M) n).inv.app ⊤
        ((laurentPullback (g ⁻¹ᵁ V).ι M (n : ℤ)).val.app (op ⊤)
          (Scheme.Modules.pullbackSection (g ⁻¹ᵁ V).ι ((laurent M).piece (n : ℤ)) (g ⁻¹ᵁ V)
            ⊤ hW (χ.sectionHom (n : ℤ) (op V) yV))) := by
  let : Stacks.Ample.IsInvertibleModule (g ⁻¹ᵁ V).toScheme
      ((pullbackFunctor (ringedSpaceHom (g ⁻¹ᵁ V).ι)).obj M) :=
    Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance
  refine (veroneseSections_chartTwisting' A V gV
    (Twisting.congrBase hgV (χ.pullback (g ⁻¹ᵁ V).ι)) n x
    (homOfLE (top_le_preimage_image_top V gV)).op).trans ?_
  refine congrArg (fun z => (powCompare
      ((pullbackFunctor (ringedSpaceHom (g ⁻¹ᵁ V).ι)).obj M) n).inv.app ⊤ z) ?_
  have hle : (opensMap (ringedSpaceHom (gV ≫ V.ι))).obj
        (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)) ≤
      (opensMap (ringedSpaceHom ((g ⁻¹ᵁ V).ι ≫ g))).obj
        (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)) := by
    rw [hgV]
  have h1 := Twisting.sectionHom_heq hgV
    (χ.pullback (g ⁻¹ᵁ V).ι)
    (Twisting.congrBase hgV (χ.pullback (g ⁻¹ᵁ V).ι))
    (Twisting.heq_congrBase hgV (χ.pullback (g ⁻¹ᵁ V).ι)).symm (n : ℤ)
    (op (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier)))
    ((x : (A.restrict V.ι).sectionRing (⊤ : V.toScheme.Opens)) (n * k)) (homOfLE hle).op
  refine (congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom
      (g ⁻¹ᵁ V).ι)).obj M)).piece (n : ℤ)).val.restrictₛₗ
      (homOfLE (top_le_preimage_image_top V gV)).op z) h1).trans ?_
  have h2 := sectionHom_resPiece A (χ.pullback (g ⁻¹ᵁ V).ι) n (V.ι_image_top).le yV
  have h3 := Twisting.sectionHom_pullback χ (g ⁻¹ᵁ V).ι (n : ℤ) (op V) yV
  refine (congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom
      (g ⁻¹ᵁ V).ι)).obj M)).piece (n : ℤ)).val.restrictₛₗ
      (homOfLE (top_le_preimage_image_top V gV)).op
      (((laurent ((pullbackFunctor (ringedSpaceHom
      (g ⁻¹ᵁ V).ι)).obj M)).piece (n : ℤ)).val.restrictₛₗ (homOfLE hle).op
      ((χ.pullback (g ⁻¹ᵁ V).ι).sectionHom
        (n : ℤ) (op (V.ι ''ᵁ (⊤ : Opens V.toScheme.toRingedSpace.carrier))) z))) hx).trans ?_
  refine (congrArg (fun z => ((laurent ((pullbackFunctor (ringedSpaceHom
      (g ⁻¹ᵁ V).ι)).obj M)).piece (n : ℤ)).val.restrictₛₗ
      (homOfLE (top_le_preimage_image_top V gV)).op
      (((laurent ((pullbackFunctor (ringedSpaceHom
      (g ⁻¹ᵁ V).ι)).obj M)).piece (n : ℤ)).val.restrictₛₗ (homOfLE hle).op z))
    (h2.trans (congrArg _ h3))).trans ?_
  refine (restrictₛₗ_three_eq_map _ _ _ _ (homOfLE hW).op _).trans ?_
  exact (PresheafOfModules.naturality_apply (laurentPullback
    (g ⁻¹ᵁ V).ι M (n : ℤ)).val (homOfLE hW).op _).symm

end ChartValue

section Cover

open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartFromRatios (VeroneseSections)
open Stacks.AlgebraicGeometry.MorphismToProjUniversal (psiSection)
open Stacks.NonvanishingOpen (nonvanishingOpen)

variable {σ R : Type u} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜] {Y : Scheme.{u}} {M N : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y M] [Stacks.Ample.IsInvertibleModule Y N]

/-- **A datum of [Stacks, Tag 01NK] carried degreewise onto a generating triple of
[Stacks, Tag 01N8] generates everywhere**: its open `U(ψ)` is the whole scheme. -/
theorem coveringOpen_eq_top_of_family (ψ : GradedSections 𝒜 M) {k : ℕ} (hk : 0 < k)
    (χ : VeroneseSections 𝒜 k N)
    (hgen : ⨆ g : 𝒜 k, nonvanishingOpen Y N (psiSection 𝒜 χ g) = ⊤)
    (Φ : ∀ n : ℕ, (natTensorPow M (n * k) : Y.Modules) ≅ natTensorPow N n)
    (hΦ : ∀ (n : ℕ) (a : 𝒜 (n * k)), (Φ n).hom.app ⊤ (ψ.toFun (n * k) a) = χ.toFun n a) :
    ψ.coveringOpen = ⊤ := by
  refine top_unique fun x _ => ?_
  have hx : x ∈ (⨆ g : 𝒜 k, nonvanishingOpen Y N (psiSection 𝒜 χ g)) := by
    rw [hgen]; trivial
  obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hx
  have h1 := Stacks.Ample.nonvanishingLocus_congr (Φ 1)
    (ψ.toFun (1 * k) ⟨(g : R) ^ 1, Stacks.MorphismToProj.HomogeneousRatios.pow_mem g.2 1⟩)
  rw [hΦ] at h1
  have hT : nonvanishingOpen Y (natTensorPow M k) (ψ.toFun k g)
      = nonvanishingOpen Y (natTensorPow N 1) (χ.pow g.2 1) :=
    (ψ.nonvanishingOpen_congr g.2 (Stacks.MorphismToProj.HomogeneousRatios.pow_mem g.2 1)
      (one_mul k).symm (pow_one _).symm).trans (Opens.ext h1.symm)
  refine ψ.nonvanishingOpenAt_le_coveringOpen_of_pos g.2 hk ?_
  show x ∈ nonvanishingOpen Y (natTensorPow M k) (ψ.toFun k g)
  rw [hT, ← Stacks.AlgebraicGeometry.MorphismToProjUniversal.nonvanishingOpen_psiSection]
  exact hg

end Cover

section PullbackSection

/-- Over the whole preimage, the pullback of a section is its image under the unit. -/
theorem pullbackSection_preimage_eq_pullbackUnit {X Y : Scheme.{u}} (b : Y ⟶ X) (G : X.Modules)
    (U : X.Opens) (s : G.val.obj (op U)) :
    Scheme.Modules.pullbackSection b G U (b ⁻¹ᵁ U) le_rfl s
      = pullbackUnit (ringedSpaceHom b) G (op U) s := by
  unfold Scheme.Modules.pullbackSection
  rw [show (homOfLE (le_refl (b ⁻¹ᵁ U))).op = 𝟙 _ from Subsingleton.elim _ _]
  simp
  rfl

end PullbackSection

/-- Two isomorphisms of sheaves of modules, applied and then undone, on a section. -/
theorem iso_iso_cancel {X : Scheme.{u}}
    {P Q R : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace)} (e₁ : P ≅ Q) (e₂ : Q ≅ R)
    (U : (Opens X.toRingedSpace.carrier)ᵒᵖ) (x : P.val.obj U) :
    (e₂.inv ≫ e₁.inv).val.app U (e₂.hom.val.app U (e₁.hom.val.app U x)) = x := by
  show ((e₁.hom ≫ e₂.hom) ≫ e₂.inv ≫ e₁.inv).val.app U x = x
  simp

section SectionHom

variable {S T : Scheme.{u}}
  {A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf S.toRingedSpace)} {f : T ⟶ S}
  {d d' : ℤ} {L L' : SheafOfModules.{u} (structureRingSheaf T.toRingedSpace)}
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L]
  [Stacks.SheafOfModules.IsInvertible T.toRingedSpace.presheaf (isSheafStruct T) L']

/-- A twisting whose component is a component of another, precomposed with a map of pieces and
postcomposed with a map of powers, acts on sections accordingly. -/
theorem Twisting.sectionHom_of_app_eq (χ' : Twisting f A d' L) (χ : Twisting f A d L') {i j : ℤ}
    (e : A.piece (i * d') ⟶ A.piece (j * d)) (φ : (laurent L').piece j ⟶ (laurent L).piece i)
    (h : χ'.app i = (pullbackFunctor (ringedSpaceHom f)).map e ≫ χ.app j ≫ φ)
    (U : (Opens S.toRingedSpace.carrier)ᵒᵖ) (a : (A.piece (i * d')).val.obj U) :
    χ'.sectionHom i U a = φ.val.app _ (χ.sectionHom j U (e.val.app U a)) := by
  rw [Twisting.sectionHom_apply, Twisting.sectionHom_apply, h]
  show φ.val.app _ ((χ.app j).val.app _
      (((pullbackFunctor (ringedSpaceHom f)).map e).val.app _ (pullbackUnit _ _ U a))) = _
  rw [pullbackUnit_naturality]

end SectionHom

section Clause

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (ψ : Twisting f (situationAlgebra A) 1 L) {W : T.Opens} {k : ℕ}
  [Epi ((ψ.pullback W.ι).app (k : ℤ))]

/-- **The quadruple of clause (2) acts on sections through `ψ`**: its degree-`n` value on a section
of `𝒜_{nk}` is the degree-`nk` value of `ψ`, pulled back to `W` and read in the powers of
`ℒ^{⊗ k}|_W`. -/
theorem restrictQuadruple_sectionHom (n : ℕ) (U : (Opens S.toRingedSpace.carrier)ᵒᵖ)
    (y : (A.piece ((n : ℤ) * (k : ℤ))).val.obj U) :
    (restrictQuadruple ψ W k).twisting.sectionHom (n : ℤ) U y
      = (powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).hom.val.app _
          ((ψ.pullback W.ι).sectionHom ((n : ℤ) * (k : ℤ)) U
            ((eqToHom (congrArg (situationAlgebra A).piece
              (show (n : ℤ) * (k : ℤ) = (n : ℤ) * (k : ℤ) * 1 by ring))).val.app U y)) := by
  let := isInvertible_piece ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)
  refine Twisting.sectionHom_of_app_eq _ (ψ.pullback W.ι) _ _ ?_ U y
  show (pullbackFunctor (ringedSpaceHom (W.ι ≫ f))).map _ ≫
      ((pullbackFunctor (ringedSpaceHom (W.ι ≫ f))).map _ ≫
        (ψ.pullback W.ι).app ((n : ℤ) * (k : ℤ)) ≫ _) = _
  rw [← Category.assoc, ← Functor.map_comp, eqToHom_trans]
  rfl

variable (W k) in
/-- `ℒ^{⊗ k}|_W` is invertible. -/
abbrev restrictPowInvertible :
    Stacks.SheafOfModules.IsInvertible W.toScheme.toRingedSpace.presheaf (isSheafStruct W.toScheme)
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)) :=
  isInvertible_piece ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)

attribute [local instance] restrictPowInvertible

variable (W k) in
/-- `ℒ^{⊗ k}|_W` further restricted to an open `Y` of `W` is invertible, in the spelling of the
ample theory. -/
abbrev partLineInvertible (Y : W.toScheme.Opens) :
    Stacks.Ample.IsInvertibleModule Y.toScheme ((pullbackFunctor (ringedSpaceHom Y.ι)).obj
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _ inferInstance

attribute [local instance] partLineInvertible

variable (L W k) in
/-- **The comparison of the powers of `(ℒ^{⊗ k}|_W)|_Y` with the pullback of `ℒ^{⊗ nk}` along
`Y ⟶ W ⟶ X`.** -/
def partPowIso (Y : W.toScheme.Opens) (n : ℕ) :
    (natTensorPow ((pullbackFunctor (ringedSpaceHom Y.ι)).obj
        (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) n : Y.toScheme.Modules)
      ≅ (Scheme.Modules.pullback (Y.ι ≫ W.ι)).obj ((laurent L).piece ((n : ℤ) * (k : ℤ))) :=
  powCompare _ n ≪≫
    (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom Y.ι)
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)) (n : ℤ)).symm ≪≫
    (Scheme.Modules.pullback Y.ι).mapIso
      ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).symm ≪≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
          ((n : ℤ) * (k : ℤ))).symm) ≪≫
    (Scheme.Modules.pullbackComp Y.ι W.ι).app _

omit [Epi ((ψ.pullback W.ι).app (k : ℤ))] in
/-- `partPowIso` undoes the conversion into the iterated powers and the pullback comparison. -/
theorem partPowIso_hom_app (Y : W.toScheme.Opens) (n : ℕ)
    (w : ((pullbackFunctor (ringedSpaceHom Y.ι)).obj ((laurent
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))).piece (n : ℤ))).val.obj
        (op ⊤)) :
    (partPowIso L W k Y n).hom.app ⊤
        ((powCompare ((pullbackFunctor (ringedSpaceHom Y.ι)).obj
          (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) n).inv.app ⊤
          ((laurentPullback Y.ι (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))
            (n : ℤ)).val.app (op ⊤) w))
      = ((Scheme.Modules.pullbackComp Y.ι W.ι).hom.app
          ((laurent L).piece ((n : ℤ) * (k : ℤ)))).val.app (op ⊤)
        (((Scheme.Modules.pullback Y.ι).map
          ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).inv ≫
            (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
              ((n : ℤ) * (k : ℤ))).inv)).val.app (op ⊤) w) := by
  exact congrArg (fun z => ((Scheme.Modules.pullbackComp Y.ι W.ι).hom.app
          ((laurent L).piece ((n : ℤ) * (k : ℤ)))).val.app (op ⊤)
        (((Scheme.Modules.pullback Y.ι).map
          ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).inv ≫
            (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
              ((n : ℤ) * (k : ℤ))).inv)).val.app (op ⊤) z))
    (comp_inv_app_inv_app_hom_app (powCompare ((pullbackFunctor (ringedSpaceHom Y.ι)).obj
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) n)
      (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom Y.ι)
        (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ)) (n : ℤ)) (op ⊤) w)

/-- **The chart-wise Veronese family of the quadruple of clause (2), read through `partPowIso`, is
the pullback along `W ∩ f^{-1}(V) ⟶ X` of the value of `ψ`.** -/
theorem partPowIso_veroneseSections (V : S.affineOpens) (n : ℕ)
    (x : (A.restrict V.1.ι).grading (⊤ : V.1.toScheme.Opens) (n * k))
    (yV : A.sectionPieces V.1 (n * k))
    (hx : (x : (A.restrict V.1.ι).sectionRing (⊤ : V.1.toScheme.Opens)) (n * k) =
      A.resPiece (V.1.ι_image_top).le (n * k) yV)
    (h : (⊤ : ((W.ι ≫ f) ⁻¹ᵁ V.1).toScheme.Opens) ≤
      (((W.ι ≫ f) ⁻¹ᵁ V.1).ι ≫ W.ι) ⁻¹ᵁ (f ⁻¹ᵁ V.1)) :
    (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V.1) n).hom.app ⊤
        ((veroneseSections (chartTwisting A V.1 ((W.ι ≫ f) ∣_ V.1)
          (partQuadruple ψ V).twisting)).toFun n x)
      = Scheme.Modules.pullbackSection (((W.ι ≫ f) ⁻¹ᵁ V.1).ι ≫ W.ι)
          ((laurent L).piece ((n : ℤ) * (k : ℤ))) (f ⁻¹ᵁ V.1) ⊤ h
          (ψ.sectionHom ((n : ℤ) * (k : ℤ)) (op V.1)
            ((eqToHom (congrArg (situationAlgebra A).piece
              (show (n : ℤ) * (k : ℤ) = (n : ℤ) * (k : ℤ) * 1 by ring))).val.app (op V.1) yV)) := by
  have hW : (⊤ : ((W.ι ≫ f) ⁻¹ᵁ V.1).toScheme.Opens) ≤
      ((W.ι ≫ f) ⁻¹ᵁ V.1).ι ⁻¹ᵁ ((W.ι ≫ f) ⁻¹ᵁ V.1) := fun z _ => z.2
  have t1 : (partQuadruple ψ V).twisting = Twisting.congrBase (partOver_comp V)
      ((restrictQuadruple ψ W k).twisting.pullback ((W.ι ≫ f) ⁻¹ᵁ V.1).ι) := rfl
  have e1 := veroneseSections_chartTwisting_restrict A (W.ι ≫ f) (restrictQuadruple ψ W k).twisting
    V.1 ((W.ι ≫ f) ∣_ V.1) (partOver_comp V) n x yV hx hW
  refine (congrArg (fun z => (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V.1) n).hom.app ⊤ z) e1).trans ?_
  have e23 : ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).inv ≫
      (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
        ((n : ℤ) * (k : ℤ))).inv).val.app _
        ((restrictQuadruple ψ W k).twisting.sectionHom (n : ℤ) (op V.1) yV)
      = Scheme.Modules.pullbackSection W.ι ((laurent L).piece ((n : ℤ) * (k : ℤ))) (f ⁻¹ᵁ V.1)
          ((W.ι ≫ f) ⁻¹ᵁ V.1) le_rfl
          (ψ.sectionHom ((n : ℤ) * (k : ℤ)) (op V.1)
            ((eqToHom (congrArg (situationAlgebra A).piece
              (show (n : ℤ) * (k : ℤ) = (n : ℤ) * (k : ℤ) * 1 by ring))).val.app (op V.1) yV)) := by
    refine (congrArg (fun z =>
      ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).inv ≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
          ((n : ℤ) * (k : ℤ))).inv).val.app _ z)
      (restrictQuadruple_sectionHom ψ (W := W) (k := k) n (op V.1) yV)).trans ?_
    refine (congrArg (fun z =>
      ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).inv ≫
        (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
          ((n : ℤ) * (k : ℤ))).inv).val.app _
        ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).hom.val.app _
          z))
      (Twisting.sectionHom_pullback ψ W.ι ((n : ℤ) * (k : ℤ)) (op V.1) _)).trans ?_
    refine (iso_iso_cancel
      (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L ((n : ℤ) * (k : ℤ)))
      (powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)) _ _).trans ?_
    exact (pullbackSection_preimage_eq_pullbackUnit W.ι _ (f ⁻¹ᵁ V.1) _).symm
  have hn := Scheme.Modules.pullbackSection_naturality ((W.ι ≫ f) ⁻¹ᵁ V.1).ι
    ((powPowIso ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ) (n : ℤ)).inv ≫
      (Stacks.TensorPowerPullback.pullbackIntPowIso (ringedSpaceHom W.ι) L
        ((n : ℤ) * (k : ℤ))).inv) ((W.ι ≫ f) ⁻¹ᵁ V.1) ⊤ hW
    ((restrictQuadruple ψ W k).twisting.sectionHom (n : ℤ) (op V.1) yV)
  refine Eq.trans ?_ (Scheme.Modules.pullbackSection_comp ((W.ι ≫ f) ⁻¹ᵁ V.1).ι W.ι
    ((laurent L).piece ((n : ℤ) * (k : ℤ))) (f ⁻¹ᵁ V.1) ((W.ι ≫ f) ⁻¹ᵁ V.1) ⊤ le_rfl hW h _)
  refine Eq.trans ?_ (congrArg (fun z => ((Scheme.Modules.pullbackComp ((W.ι ≫ f) ⁻¹ᵁ V.1).ι
      W.ι).hom.app ((laurent L).piece ((n : ℤ) * (k : ℤ)))).val.app (op ⊤)
    (Scheme.Modules.pullbackSection ((W.ι ≫ f) ⁻¹ᵁ V.1).ι _ ((W.ι ≫ f) ⁻¹ᵁ V.1) ⊤ hW z)) e23)
  refine Eq.trans ?_ (congrArg (fun z => ((Scheme.Modules.pullbackComp ((W.ι ≫ f) ⁻¹ᵁ V.1).ι
      W.ι).hom.app ((laurent L).piece ((n : ℤ) * (k : ℤ)))).val.app (op ⊤) z) hn)
  exact partPowIso_hom_app _ _ _

omit [Epi ((ψ.pullback W.ι).app (k : ℤ))] in
/-- **The datum of clause (2) over `V`, read through `restrictPullIso`, is the pullback along
`W ∩ f^{-1}(V) ⟶ X` of the value of `ψ`.** -/
theorem restrictPullIso_partDatum (V : S.Opens) (m : ℕ) (a : A.grading V m)
    (h : (⊤ : ((W.ι ≫ f) ⁻¹ᵁ V).toScheme.Opens) ≤
      (partInclusion (W := W) V ≫ (f ⁻¹ᵁ V).ι) ⁻¹ᵁ (f ⁻¹ᵁ V)) :
    (restrictPullIso L (f ⁻¹ᵁ V) (partInclusion (W := W) V) m).hom.app ⊤
        ((partDatum ψ V).toFun m a)
      = Scheme.Modules.pullbackSection (partInclusion (W := W) V ≫ (f ⁻¹ᵁ V).ι)
          (Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (m : ℤ)) (f ⁻¹ᵁ V) ⊤ h
          (ψ.sectionHom (m : ℤ) (op V)
            ((pieceCast (A := A) (m : ℤ)).val.app (op V) ((a : A.sectionRing V) m))) := by
  refine (restrictPullIso_pullSection L (f ⁻¹ᵁ V) (partInclusion (W := W) V) m _ h).trans ?_
  refine congrArg (Scheme.Modules.pullbackSection (partInclusion (W := W) V ≫ (f ⁻¹ᵁ V).ι)
    (Stacks.AmpleProjectiveImmersion.tensorPowerModule T L (m : ℤ)) (f ⁻¹ᵁ V) ⊤ h) ?_
  refine (congrArg (fun z => (powCompare L m).hom.app (f ⁻¹ᵁ V) z)
    (toGradedPowerMap_value ψ m V ((a : A.sectionRing V) m))).trans ?_
  exact (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app (powCompare L m)
      (f ⁻¹ᵁ V) _)

variable (W k) in
/-- **The degreewise comparison of the two data over `V`**: the powers of the pulled-back
`ℒ|_{f^{-1}(V)}` in degree `nk` and the powers of `(ℒ^{⊗ k}|_W)|_{W ∩ f^{-1}(V)}` in degree `n`
are both the pullback of `ℒ^{⊗ nk}` to `W ∩ f^{-1}(V)`. -/
def partFamily (V : S.Opens) (n : ℕ) :
    (natTensorPow ((Scheme.Modules.pullback (partInclusion (W := W) V)).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L)) (n * k) : ((W.ι ≫ f) ⁻¹ᵁ V).toScheme.Modules)
      ≅ natTensorPow ((pullbackFunctor (ringedSpaceHom ((W.ι ≫ f) ⁻¹ᵁ V).ι)).obj
          (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) n :=
  restrictPullIso L (f ⁻¹ᵁ V) (partInclusion (W := W) V) (n * k) ≪≫
    (Scheme.Modules.pullbackCongr (partInclusion_ι (W := W) (f := f) V)).app _ ≪≫
    (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V) n).symm

/-- An isomorphism undone, on global sections. -/
theorem inv_app_hom_app_top {Z : Scheme.{u}} {P Q : Z.Modules} (e : P ≅ Q) (w : Γ(P, ⊤)) :
    e.inv.app ⊤ (e.hom.app ⊤ w) = w :=
  Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app e.symm ⊤ w

/-- **`partFamily` carries the datum of clause (2) over `V` to the chart-wise Veronese family of
the quadruple of clause (2)**, degreewise. -/
theorem partFamily_toFun (V : S.affineOpens)
    (χ : Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections (A.grading V.1) k
      ((pullbackFunctor (ringedSpaceHom ((W.ι ≫ f) ⁻¹ᵁ V.1).ι)).obj
        (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))))
    (hχ : HEq (veroneseSections (chartTwisting A V.1 ((W.ι ≫ f) ∣_ V.1)
      (partQuadruple ψ (W := W) (k := k) V).twisting)) χ)
    (n : ℕ) (y : A.grading V.1 (n * k)) :
    (partFamily W k V.1 n).hom.app ⊤ ((partDatum ψ V.1).toFun (n * k) y) = χ.toFun n y := by
  obtain ⟨x, hx⟩ :=
    Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.exists_restrict_grading_heq
      V.1 V.1 V.1.ι_image_top y
  have e1 : χ.toFun n y = (veroneseSections (chartTwisting A V.1 ((W.ι ≫ f) ∣_ V.1)
      (partQuadruple ψ (W := W) (k := k) V).twisting)).toFun n x :=
    (veroneseSections_restrict_toFun_heq A V.1 _ V.1.ι_image_top _ χ hχ n x y hx).symm
  have hxU := Stacks.AlgebraicGeometry.RelativeProjTwistChartBridge.component_eq_resPiece_of_heq
    V.1.ι_image_top x y hx
  have h : (⊤ : ((W.ι ≫ f) ⁻¹ᵁ V.1).toScheme.Opens) ≤
      (((W.ι ≫ f) ⁻¹ᵁ V.1).ι ≫ W.ι) ⁻¹ᵁ (f ⁻¹ᵁ V.1) := fun z _ => z.2
  have h' : (⊤ : ((W.ι ≫ f) ⁻¹ᵁ V.1).toScheme.Opens) ≤
      (partInclusion (W := W) V.1 ≫ (f ⁻¹ᵁ V.1).ι) ⁻¹ᵁ (f ⁻¹ᵁ V.1) := by
    rw [partInclusion_ι]; exact h
  have e2 := partPowIso_veroneseSections ψ (W := W) (k := k) V n x _ hxU h
  have e3 := restrictPullIso_partDatum ψ (W := W) V.1 (n * k) y h'
  have e4 := Scheme.Modules.pullbackSection_congr (partInclusion_ι (W := W) (f := f) V.1)
    (Stacks.AmpleProjectiveImmersion.tensorPowerModule T L ((n * k : ℕ) : ℤ)) (f ⁻¹ᵁ V.1) ⊤ h' h
    (ψ.sectionHom ((n * k : ℕ) : ℤ) (op V.1)
      ((pieceCast (A := A) ((n * k : ℕ) : ℤ)).val.app (op V.1) ((y : A.sectionRing V.1) (n * k))))
  rw [e1]
  refine Eq.trans ?_ (inv_app_hom_app_top (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V.1) n) _)
  refine Eq.trans ?_ (congrArg (fun z => (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V.1) n).inv.app ⊤ z)
    e2).symm
  show (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V.1) n).inv.app ⊤
      (((Scheme.Modules.pullbackCongr (partInclusion_ι (W := W) (f := f) V.1)).hom.app _).val.app
        (op ⊤)
        ((restrictPullIso L (f ⁻¹ᵁ V.1) (partInclusion (W := W) V.1) (n * k)).hom.app ⊤
          ((partDatum ψ V.1).toFun (n * k) y))) = _
  rw [e3]
  exact congrArg (fun z => (partPowIso L W k ((W.ι ≫ f) ⁻¹ᵁ V.1) n).inv.app ⊤ z) e4

/-- **Over an affine open `V` of the base, clause (2) holds on the part of `W` over `V`**: the
pulled-back datum of [Stacks, Tag 01NK] generates everywhere there, and the morphism of the
relative homogeneous spectrum agrees with its morphism. -/
theorem partDatum_coveringOpen_and_glued (hk : 0 < k) (V : S.affineOpens) :
    (partDatum (W := W) ψ V.1).coveringOpen = ⊤ ∧
      (partDatum (W := W) ψ V.1).coveringOpen.ι ≫ ((W.ι ≫ f) ⁻¹ᵁ V.1).ι
          ≫ F.classifyingMorphism A
            (F.mk (W.ι ≫ f) (by exact_mod_cast hk) (restrictQuadruple ψ W k))
        = (partDatum (W := W) ψ V.1).glued ≫ (relativeProj A).chart V.1 V.2 := by
  have : IsAffine V.1.toScheme := V.2
  obtain ⟨χ, hχ⟩ := exists_veroneseSections_restrict A V.1
    (L := (pullbackFunctor (ringedSpaceHom ((W.ι ≫ f) ⁻¹ᵁ V.1).ι)).obj
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) V.1.ι_image_top
    (veroneseSections (chartTwisting A V.1 ((W.ι ≫ f) ∣_ V.1)
      (partQuadruple ψ (W := W) (k := k) V).twisting))
  have hgen := iSup_nonvanishingOpen_psiSection_restrict_heq A V.1
    (L := (pullbackFunctor (ringedSpaceHom ((W.ι ≫ f) ⁻¹ᵁ V.1).ι)).obj
      (powModule ((pullbackFunctor (ringedSpaceHom W.ι)).obj L) (k : ℤ))) V.1.ι_image_top _ χ hχ
    (Quadruple.iSup_nonvanishingOpen_psiSection_eq_top (B := A.restrict V.1.ι) (d := k)
      (fun n => (A.restrict V.1.ι).isQuasicoherent n)
      (((partQuadruple ψ (W := W) (k := k) V).baseChangeDown V.1.ι ((W.ι ≫ f) ∣_ V.1)
        (situationAlgebra A) (k : ℤ)).algebraTransport
        (unitalHomInverse (restrictPullbackUnitalHom A V.1.ι)
          (isIso_restrictPullbackUnitalHom_app_forall A V.1.ι))
        (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A V.1.ι)
          (isIso_restrictPullbackUnitalHom_app_forall A V.1.ι))))
  have ha : toProj (A.grading V.1)
        (Fd.chartEquiv A V.1 V.2 hk _ (partClass ψ (W := W) (k := k) V))
      = toProj (A.grading V.1)
          (Stacks.AlgebraicGeometry.ProjTripleClassifying.classifyingHom (A.grading V.1) hk χ
            hgen) := by
    rw [partClass, Fd.chartClass_mk]
    exact Fd.toProj_chartEquiv_mk A V.1 V.2 hk ((W.ι ≫ f) ∣_ V.1)
      (((partQuadruple ψ (W := W) (k := k) V).baseChangeDown V.1.ι ((W.ι ≫ f) ∣_ V.1)
        (situationAlgebra A) (k : ℤ)).algebraTransport
        (unitalHomInverse (restrictPullbackUnitalHom A V.1.ι)
          (isIso_restrictPullbackUnitalHom_app_forall A V.1.ι))
        (isIso_unitalHomInverse_app (restrictPullbackUnitalHom A V.1.ι)
          (isIso_restrictPullbackUnitalHom_app_forall A V.1.ι))) rfl χ hχ hgen
  have hcore := coveringOpen_ι_toProj_classifyingHom (partDatum (W := W) ψ V.1) hk χ hgen
    (partFamily W k V.1) (partFamily_toFun ψ V χ hχ)
  refine ⟨coveringOpen_eq_top_of_family (partDatum (W := W) ψ V.1) hk χ hgen
    (partFamily W k V.1) (partFamily_toFun ψ V χ hχ), ?_⟩
  rw [partOver_ι_classifyingMorphism ψ hk V, ha, ← hcore]
  simp only [Category.assoc]

end Clause

section Statement

variable {S T : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : T ⟶ S}
  {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]

/-- **Clause (2) of [Stacks, Tag 01O9].** Let `S` be a scheme, `𝒜` a quasi-coherent graded
`𝒪_S`-algebra, `f : X ⟶ S` a morphism, `ℒ` an invertible `𝒪_X`-module and
`ψ : f^*𝒜 ⟶ ⨁_n ℒ^{⊗ n}` a homomorphism of graded `𝒪_X`-algebras. For every `k ≥ 1` and every
open `W ⊆ X` on which the degree-`k` component `ψ|_W : f^*𝒜_k|_W ⟶ ℒ^{⊗ k}|_W` is surjective,
`W` lies in `U(ψ)`, and the restriction to `W` of `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` is the morphism
`W ⟶ Proj_S(𝒜)` that the construction of the relative homogeneous spectrum attaches to the
quadruple `(k, f|_W, ℒ^{⊗ k}|_W, ψ|_{𝒜^{(k)}})`, that is, the morphism classifying its point of
the functor that `Proj_S(𝒜)` represents. -/
theorem clauseTwo (ψ : Twisting f (situationAlgebra A) 1 L) {k : ℕ} (hk : 0 < k) (W : T.Opens)
    [Epi ((ψ.pullback W.ι).app (k : ℤ))] :
    ∃ h : W ≤ (toGradedPowerMap ψ).coveringOpen,
      T.homOfLE h ≫ (toGradedPowerMap ψ).globalMorphism (relativeProj A)
        = F.classifyingMorphism A
            (F.mk (W.ι ≫ f) (by exact_mod_cast hk) (restrictQuadruple ψ W k)) :=
  clauseTwo_of_parts ψ hk (fun V => (partDatum_coveringOpen_and_glued ψ hk V).1)
    (fun V => (partDatum_coveringOpen_and_glued ψ hk V).2)

end Statement

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
