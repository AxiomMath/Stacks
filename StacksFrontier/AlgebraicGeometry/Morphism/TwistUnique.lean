module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphism.TwistPsi
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaUnique
public import StacksFrontier.AlgebraicGeometry.TwistRigidity.Pointwise

/-!
# Tag 07ZG: `θ` is determined by condition (1)

Let `ψ : A ⟶ B` be a homomorphism of quasi-coherent graded `𝒪_S`-algebras, `r_ψ : U(ψ) ⟶ Proj_S(A)`
the morphism of Tag 07ZG and `ι : U(ψ) ⟶ Proj_S(B)` the inclusion. A map of `ℤ`-graded algebras
`θ' : r_ψ^*(⨁_d 𝒪_{Proj_S(A)}(d)) ⟶ ι^*(⨁_d 𝒪_{Proj_S(B)}(d))` which carries the inverse image of
`ψ_A(a)`, for every homogeneous section `a` of `A`, to the inverse image of `ψ_B(ψ(a))` (condition
(1) of Tag 01MY, `Stacks.AlgebraicGeometry.Tag07ZGTwist.MapsPsi`) is the map `θ` of Tag 07ZG.

Over the chart image of a standard open `D₊(g)` every section `t` of `𝒪(n)` satisfies
`ψ(g^j) · t = ψ(x)`; condition (1) fixes the images of `ψ(g^j)` and `ψ(x)`, multiplicativity fixes
`θ'(ψ(g^j)) · θ'(t)`, and multiplication by `ψ_B(ψ(g^j))` is injective over the open of `U(ψ)`
above `D₊(g)`, because `r_ψ` carries that open into the chart image of `D₊(ψ(g))`.

This is the tool that compares two descriptions of `θ`: it reduces any compatibility of `θ`
with a change of algebras to a computation on the sections `ψ(a)`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.MapsPsi`: condition (1).

## Main results

* `Stacks.AlgebraicGeometry.Tag07ZGTwist.mapsPsi_relativeTwistAlgebraHom`: `θ` satisfies it.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.MapsPsi.eq`: two maps of graded algebras satisfying it
  are equal, and `Stacks.AlgebraicGeometry.Tag07ZGTwist.eq_relativeTwistAlgebraHom_of_mapsPsi`:
  such a map is `θ`.
* `Stacks.AlgebraicGeometry.Tag07ZGTwist.ι_image_relativeMapHom_preimage_le`: `r_ψ` carries the
  part of `U(ψ)` over the chart image of `D₊(g)` into the chart image of `D₊(ψ(g))`.

## References

* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u w

namespace Stacks.AlgebraicGeometry.TwistRigidity

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjTwists

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **Multiplication by the section of `c` is injective over `D₊(c)`**, on the absolute twists. -/
theorem eq_of_degreeSectionOn_mul_eq (k : ℕ) {c : S} (hc : c ∈ 𝒜 k) (n : ℤ)
    {V : Opens (ProjectiveSpectrum.top 𝒜)} (hV : V ≤ Proj.basicOpen 𝒜 c)
    {a b : (twistingSheaf 𝒜 n).val.obj (op V)}
    (h : absoluteTwistProduct 𝒜 (k : ℤ) n V (degreeSectionOn 𝒜 k hc V) a =
      absoluteTwistProduct 𝒜 (k : ℤ) n V (degreeSectionOn 𝒜 k hc V) b) : a = b := by
  refine Subtype.ext (funext fun y => ?_)
  have hy := ((absoluteTwistProduct_apply 𝒜 (k : ℤ) n V _ a y).symm.trans
    ((twist_val_congr 𝒜 h y).trans (absoluteTwistProduct_apply 𝒜 (k : ℤ) n V _ b y)))
  rw [degreeSectionOn_apply] at hy
  exact eq_of_mkOne_mul_eq _ (hV y.2) hy

end Stacks.AlgebraicGeometry.TwistRigidity

namespace Stacks.AlgebraicGeometry.Tag07ZGTwist

open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp)
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjMapDomain Stacks.AlgebraicGeometry.Tag07ZGMorphism
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap (twD Otw psiU
  chart_image_le chartIso_hom_mul chartIso_hom_psiU exists_psiU_mul_eq)
open Stacks.AlgebraicGeometry.TwistRigidity (eq_of_degreeSectionOn_mul_eq)

variable {S : Scheme.{u}}

/-- Multiplication by `ψ(b)` is injective on the sections of the relative twists over the image
under a chart of an open inside `D₊(b)`. -/
theorem eq_of_psiU_mul_eq (B : SheafGradedAlgebra S) (V : S.Opens) (hV : IsAffineOpen V) (k : ℕ)
    (b : Γ(B.piece (k : ℤ), V)) (n : ℤ) {W₁ : (AlgebraicGeometry.Proj (B.grading V)).Opens}
    (hW : W₁ ≤ AlgebraicGeometry.Proj.basicOpen (B.grading V)
      (DirectSum.of (B.sectionPieces V) k b))
    {s t : Γ(Otw B n, (relativeProj B).chart V hV ''ᵁ W₁)}
    (h : ((twD B).algebra.mul (k : ℤ) n).app (op ((relativeProj B).chart V hV ''ᵁ W₁))
        ((Otw B k).presheaf.map (homOfLE (chart_image_le V hV W₁)).op (psiU B k V b)) s =
      ((twD B).algebra.mul (k : ℤ) n).app (op ((relativeProj B).chart V hV ''ᵁ W₁))
        ((Otw B k).presheaf.map (homOfLE (chart_image_le V hV W₁)).op (psiU B k V b)) t) :
    s = t := by
  have hcancel : ∀ x : Γ(Otw B n, (relativeProj B).chart V hV ''ᵁ W₁),
      ((twD B).chartData.chartIso V hV n).inv.app W₁
        (((twD B).chartData.chartIso V hV n).hom.app W₁ x) = x := fun x =>
    (ConcreteCategory.congr_hom (congrArg (fun φ => Scheme.Modules.Hom.app φ W₁)
      ((twD B).chartData.chartIso V hV n).hom_inv_id) x).trans rfl
  have key : ∀ x : Γ(Otw B n, (relativeProj B).chart V hV ''ᵁ W₁),
      ((twD B).chartData.chartIso V hV ((k : ℤ) + n)).hom.app W₁
        (((twD B).algebra.mul (k : ℤ) n).app (op ((relativeProj B).chart V hV ''ᵁ W₁))
          ((Otw B k).presheaf.map (homOfLE (chart_image_le V hV W₁)).op (psiU B k V b)) x) =
      Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct (B.grading V) (k : ℤ) n W₁
        (Stacks.AlgebraicGeometry.TwistRigidity.degreeSectionOn (B.grading V) k
          (B.of_mem_grading V b) W₁)
        (((twD B).chartData.chartIso V hV n).hom.app W₁ x) := fun x =>
    (chartIso_hom_mul V hV (k : ℤ) n W₁ _ x).trans
      ((congrArg (fun z => ((Stacks.AlgebraicGeometry.ProjConeTwist.integerTwistAlgebra
          (B.grading V)).mul (k : ℤ) n).app (op W₁) z
          (((twD B).chartData.chartIso V hV n).hom.app W₁ x))
        (chartIso_hom_psiU V hV k W₁ b)).trans
      (Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.absoluteTwistProduct_eq_mul
        (B.grading V) (k : ℤ) n W₁ _ _).symm)
  have h2 := (key s).symm.trans
    ((congrArg (((twD B).chartData.chartIso V hV ((k : ℤ) + n)).hom.app W₁) h).trans (key t))
  exact (hcancel s).symm.trans ((congrArg _
    (eq_of_degreeSectionOn_mul_eq (B.grading V) k (B.of_mem_grading V b) n hW h2)).trans
      (hcancel t))

/-- The product of an inverse image of a sheaf of graded algebras, on pulled-back sections. -/
private theorem pullbackGradedAlgebra_mul_pullbackSection_aux {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace))
    (i j : ℤ) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (a : (G.piece i).val.obj (op U)) (b : (G.piece j).val.obj (op U)) :
    ((Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom G).mul i j).app (op V)
        (Scheme.Modules.pullbackSection f (G.piece i) U V h a)
        (Scheme.Modules.pullbackSection f (G.piece j) U V h b) =
      Scheme.Modules.pullbackSection f (G.piece (i + j)) U V h ((G.mul i j).app (op U) a b) :=
  (((Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom G).mul i j).naturality
      (homOfLE h).op _ _).symm.trans
    (congrArg (((Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom G).piece
        (i + j)).val.map (homOfLE h).op)
      (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit f.toLRSHom.toShHom G i j U a b))

/-- Cancellation in the inverse image of a sheaf of graded algebras along an open immersion, from
cancellation on the image. -/
theorem eq_of_mul_pullbackSection_eq {Y Z : Scheme.{u}} (ι : Y ⟶ Z) [IsOpenImmersion ι]
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Z.toRingedSpace))
    (k n : ℤ) (O : Y.Opens) (c₀ : (G.piece k).val.obj (op (ι ''ᵁ O)))
    (hc : ∀ s t : (G.piece n).val.obj (op (ι ''ᵁ O)),
      (G.mul k n).app (op (ι ''ᵁ O)) c₀ s = (G.mul k n).app (op (ι ''ᵁ O)) c₀ t → s = t)
    {a a' : ((Stacks.RingedSpace.pullbackGradedAlgebra ι.toLRSHom.toShHom G).piece n).val.obj
      (op O)}
    (h : ((Stacks.RingedSpace.pullbackGradedAlgebra ι.toLRSHom.toShHom G).mul k n).app (op O)
        (Scheme.Modules.pullbackSection ι (G.piece k) (ι ''ᵁ O) O (ι.preimage_image_eq O).ge c₀) a =
      ((Stacks.RingedSpace.pullbackGradedAlgebra ι.toLRSHom.toShHom G).mul k n).app (op O)
        (Scheme.Modules.pullbackSection ι (G.piece k) (ι ''ᵁ O) O (ι.preimage_image_eq O).ge c₀)
          a') :
    a = a' := by
  let N := Stacks.RingedSpace.pullbackGradedAlgebra ι.toLRSHom.toShHom G
  let E : ∀ m : ℤ, (G.piece m).val.obj (op (ι ''ᵁ O)) → (N.piece m).val.obj (op O) := fun m x =>
    Scheme.Modules.pullbackSection ι (G.piece m) (ι ''ᵁ O) O (ι.preimage_image_eq O).ge x
  let e := fun m : ℤ => (Scheme.Modules.restrictFunctorIsoPullback ι).app (G.piece m)
  have hinvE : ∀ (m : ℤ) (x : (G.piece m).val.obj (op (ι ''ᵁ O))),
      ((e m).inv).val.app (op O) (E m x) = x := fun m x =>
    (Scheme.Modules.restrictFunctorIsoPullback_inv_pullbackSection ι (G.piece m) (ι ''ᵁ O) O
      (ι.preimage_image_eq O).ge le_rfl x).trans (by
        rw [show (homOfLE (le_rfl : ι ''ᵁ O ≤ ι ''ᵁ O)).op = 𝟙 _ from rfl]
        exact (G.piece m).val.map_id_apply _ x)
  have hhi : ∀ (m : ℤ) (z : (N.piece m).val.obj (op O)),
      ((e m).hom).val.app (op O) (((e m).inv).val.app (op O) z) = z := fun m z =>
    congrArg (fun φ => PresheafOfModules.Hom.app (SheafOfModules.Hom.val φ) (op O) z)
      (e m).inv_hom_id
  have hE : ∀ (m : ℤ) (z : (N.piece m).val.obj (op O)), E m (((e m).inv).val.app (op O) z) = z :=
    fun m z => (hhi m _).symm.trans ((congrArg (((e m).hom).val.app (op O)) (hinvE m _)).trans
      (hhi m z))
  have hmul := pullbackGradedAlgebra_mul_pullbackSection_aux ι G k n (ι ''ᵁ O) O
    (ι.preimage_image_eq O).ge c₀
  have h1 := (hmul _).symm.trans (((congrArg _ (hE n a)).trans
    (h.trans (congrArg _ (hE n a')).symm)).trans (hmul _))
  have h2 := hc _ _ ((hinvE _ _).symm.trans ((congrArg _ h1).trans (hinvE _ _)))
  exact (hE n a).symm.trans ((congrArg (E n) h2).trans (hE n a'))

open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain in
/-- **`r_ψ` carries the standard opens of the charts of `U(ψ)` into those of `Proj_S(A)`**, read
on `Proj_S(B)`: a point of `U(ψ)` whose image under `r_ψ` lies in the chart image of `D₊(g)` lies
in the chart image of `D₊(ψ g)`. -/
theorem ι_image_relativeMapHom_preimage_le {A B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (V : S.Opens) (hV : IsAffineOpen V) {e : ℕ}
    {g : A.sectionRing V} (hg : g ∈ A.grading V e) (he : 0 < e) :
    ψ.relativeMapDomain.ι ''ᵁ (relativeMapHom ψ ⁻¹ᵁ
        ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) ≤
      (relativeProj B).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (B.grading V) (ψ.sectionHom V g) := by
  let U : S.affineOpens := ⟨V, hV⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨z, hz, hzy₀⟩ := hy
  have hzy : (relativeProj A).chart V hV z = relativeMapHom ψ y := hzy₀
  -- the image of `y` lies over `V`
  have hyV : (relativeProj B).toBase (ψ.relativeMapDomain.ι y) ∈ V := by
    rw [← Scheme.Hom.comp_apply, ← relativeMapHom_comp_toBase, Scheme.Hom.comp_apply, ← hzy,
      toBase_chart_apply]
    exact (projInclusionToOpen A V hV z).2
  obtain ⟨p, rfl⟩ : y ∈ (pieceIncl ψ U).opensRange := by
    rw [opensRange_homOfLE]
    exact (chartImage_eq_inf ψ U).ge ⟨y.2, hyV⟩
  let w := (chartDomainIso ψ U).inv p
  have hr : relativeMapHom ψ (pieceIncl ψ U p) =
      (relativeProj A).chart V hV (mapHom (A.grading V) (B.grading V) (ψ.sectionHom V) w) := by
    rw [← Scheme.Hom.comp_apply, pieceIncl_comp_relativeMapHom]
    rfl
  have hι : ψ.relativeMapDomain.ι (pieceIncl ψ U p) =
      (relativeProj B).chart V hV
        ((mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).ι w) := by
    rw [← Scheme.Hom.comp_apply, pieceIncl_comp_ι]
    rfl
  have hmz : mapHom (A.grading V) (B.grading V) (ψ.sectionHom V) w = z :=
    ((relativeProj A).chart V hV).isOpenEmbedding.injective (hr.symm.trans hzy.symm)
  have hw : w ∈ mapHom (A.grading V) (B.grading V) (ψ.sectionHom V) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g := by
    show mapHom (A.grading V) (B.grading V) (ψ.sectionHom V) w ∈
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g
    rwa [hmz]
  rw [mapHom_preimage_basicOpen _ _ _ g e hg he] at hw
  exact ⟨(mapDomain (A.grading V) (B.grading V) (ψ.sectionHom V)).ι w, hw, hι.symm⟩

/-- Pulling back the restriction of a section is pulling back the section. -/
theorem pullbackSection_map {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) {U U' : X.Opens}
    (i : U' ≤ U) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U') (a : M.val.obj (op U)) :
    Scheme.Modules.pullbackSection f M U' V h (M.val.map (homOfLE i).op a) =
      Scheme.Modules.pullbackSection f M U V (h.trans (f.preimage_mono i)) a := by
  unfold Scheme.Modules.pullbackSection
  refine (congrArg (((Scheme.Modules.pullback f).obj M).val.map (homOfLE h).op)
    (PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val (homOfLE i).op a)).trans ?_
  refine (PresheafOfModules.map_comp_apply ((Scheme.Modules.pullback f).obj M).val
    (homOfLE (f.preimage_mono i)).op (homOfLE h).op _).symm.trans ?_
  congr 2

/-- The product of an inverse image of a sheaf of graded algebras, on pulled-back sections. -/
theorem pullbackGradedAlgebra_mul_pullbackSection {X Y : Scheme.{u}} (f : Y ⟶ X)
    (G : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace))
    (i j : ℤ) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (a : (G.piece i).val.obj (op U)) (b : (G.piece j).val.obj (op U)) :
    ((Stacks.RingedSpace.pullbackGradedAlgebra f.toLRSHom.toShHom G).mul i j).app (op V)
        (Scheme.Modules.pullbackSection f (G.piece i) U V h a)
        (Scheme.Modules.pullbackSection f (G.piece j) U V h b) =
      Scheme.Modules.pullbackSection f (G.piece (i + j)) U V h ((G.mul i j).app (op U) a b) :=
  pullbackGradedAlgebra_mul_pullbackSection_aux f G i j U V h a b

/-- A degreewise family of functions preserves heterogeneous equality across equal degrees. -/
theorem heq_apply_of_heq {F G : ℤ → Type*} (φ : ∀ k, F k → G k) {k k' : ℤ} (h : k = k')
    {a : F k} {b : F k'} (hab : HEq a b) : HEq (φ k a) (φ k' b) := by
  subst h
  rw [eq_of_heq hab]

/-- Multiplication by `ψ(b)` is injective on the sections of the relative twists over any open
inside the chart image of `D₊(b)`. -/
theorem eq_of_psiU_mul_eq' (B : SheafGradedAlgebra S) (V : S.Opens) (hV : IsAffineOpen V) (k : ℕ)
    (b : Γ(B.piece (k : ℤ), V)) (n : ℤ) {O : (relativeProj B).scheme.Opens}
    (hO : O ≤ (relativeProj B).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (B.grading V)
      (DirectSum.of (B.sectionPieces V) k b))
    (hOV : O ≤ (relativeProj B).toBase ⁻¹ᵁ V) {s t : Γ(Otw B n, O)}
    (h : ((twD B).algebra.mul (k : ℤ) n).app (op O)
        ((Otw B k).presheaf.map (homOfLE hOV).op (psiU B k V b)) s =
      ((twD B).algebra.mul (k : ℤ) n).app (op O)
        ((Otw B k).presheaf.map (homOfLE hOV).op (psiU B k V b)) t) :
    s = t := by
  obtain ⟨W₁, rfl⟩ : ∃ W₁, (relativeProj B).chart V hV ''ᵁ W₁ = O := by
    refine ⟨(relativeProj B).chart V hV ⁻¹ᵁ O, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.image_top_eq_opensRange]
    exact inf_eq_right.mpr (hO.trans (Scheme.Hom.image_mono _ le_top))
  exact eq_of_psiU_mul_eq B V hV k b n
    (((relativeProj B).chart V hV).image_le_image_iff _ _ |>.mp hO) h

/-- **Cancellation in `ι^*(⨁_d 𝒪_{Proj_S(B)}(d))` by a section `ψ_B(b)`**, over an open of `U(ψ)`
whose image lies in the chart image of `D₊(b)`. -/
theorem eq_of_mul_psiU_pullbackSection_eq {A B : SheafGradedAlgebra S}
    (ψ : SheafGradedAlgebraHom A B) (V : S.Opens) (hV : IsAffineOpen V) (k : ℕ)
    (b : Γ(B.piece (k : ℤ), V)) (n : ℤ) {O : ψ.relativeMapDomain.toScheme.Opens}
    (hO : ψ.relativeMapDomain.ι ''ᵁ O ≤ (relativeProj B).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (B.grading V) (DirectSum.of (B.sectionPieces V) k b))
    (hOV : O ≤ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V))
    {a a' : ((Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
      (twistAlgebra B)).piece n).val.obj (op O)}
    (h : ((Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
          (twistAlgebra B)).mul (k : ℤ) n).app (op O)
        (Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B k)
          ((relativeProj B).toBase ⁻¹ᵁ V) O hOV (psiU B k V b)) a =
      ((Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
          (twistAlgebra B)).mul (k : ℤ) n).app (op O)
        (Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B k)
          ((relativeProj B).toBase ⁻¹ᵁ V) O hOV (psiU B k V b)) a') :
    a = a' := by
  have hiV : ψ.relativeMapDomain.ι ''ᵁ O ≤ (relativeProj B).toBase ⁻¹ᵁ V :=
    (Scheme.Hom.image_mono _ hOV).trans (Scheme.Hom.image_preimage_le _ _)
  have e := pullbackSection_map ψ.relativeMapDomain.ι (relativeTwist B k) hiV O
    (ψ.relativeMapDomain.ι.preimage_image_eq O).ge (psiU B k V b)
  rw [← e] at h
  exact eq_of_mul_pullbackSection_eq ψ.relativeMapDomain.ι (twistAlgebra B) (k : ℤ) n O _
    (fun s t hst => eq_of_psiU_mul_eq' B V hV k b n hO hiV hst) h

section Unique

variable {A B : SheafGradedAlgebra S} (ψ : SheafGradedAlgebraHom A B)

/-- **Condition (1) of Tag 01MY for a map of graded algebras on the twists over `U(ψ)`**: it
carries the inverse image along `r_ψ` of the section `ψ_A(a)` attached to a homogeneous section `a`
of `A` to the inverse image along the inclusion of `U(ψ)` of `ψ_B(ψ(a))`. -/
def MapsPsi (θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))) : Prop :=
  ∀ (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V)),
    (θ'.app (d : ℤ)).val.app (op (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A d)
          ((relativeProj A).toBase ⁻¹ᵁ V) _ le_rfl (psiU A d V a)) =
      Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B d)
        ((relativeProj B).toBase ⁻¹ᵁ V) _ (relativeMapHom_preimage_toBase ψ V).le
        (psiU B d V ((ψ.app (d : ℤ)).app V a))

/-- The map `θ` of Tag 07ZG satisfies condition (1). -/
theorem mapsPsi_relativeTwistAlgebraHom : MapsPsi ψ (relativeTwistAlgebraHom ψ) := by
  intro d V a
  refine Eq.trans ?_ (relativeTwistMap_unitApp_psiU ψ d V a)
  unfold Scheme.Modules.pullbackSection
  exact congrArg ((relativeTwistMap ψ d).val.app _)
    (PresheafOfModules.map_id_apply
      ((Scheme.Modules.pullback (relativeMapHom ψ)).obj (relativeTwist A d)).val
      (op (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))) _)

/-- Condition (1) restricted to a smaller open. -/
theorem MapsPsi.app_pullbackSection {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))} (hθ : MapsPsi ψ θ') (d : ℕ) (V : S.Opens) (a : Γ(A.piece (d : ℤ), V))
    {W : (relativeProj A).scheme.Opens} (hW : W ≤ (relativeProj A).toBase ⁻¹ᵁ V)
    (hO : relativeMapHom ψ ⁻¹ᵁ W ≤ ψ.relativeMapDomain.ι ⁻¹ᵁ ((relativeProj B).toBase ⁻¹ᵁ V)) :
    (θ'.app (d : ℤ)).val.app (op (relativeMapHom ψ ⁻¹ᵁ W))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A d) W _ le_rfl
          ((relativeTwist A d).val.map (homOfLE hW).op (psiU A d V a))) =
      Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B d)
        ((relativeProj B).toBase ⁻¹ᵁ V) _ hO (psiU B d V ((ψ.app (d : ℤ)).app V a)) := by
  have hle : relativeMapHom ψ ⁻¹ᵁ W ≤ relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) :=
    (relativeMapHom ψ).preimage_mono hW
  refine (congrArg ((θ'.app (d : ℤ)).val.app (op (relativeMapHom ψ ⁻¹ᵁ W)))
    ((pullbackSection_map _ _ hW _ le_rfl _).trans
      (Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink _ _ _ _ _ le_rfl hle
        hle _).symm)).trans ?_
  refine (PresheafOfModules.naturality_apply (θ'.app (d : ℤ)).val (homOfLE hle).op _).trans ?_
  refine (congrArg _ (hθ d V a)).trans ?_
  exact Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink _ _ _ _ _ _ _ _ _

/-- **Two maps with condition (1) agree over the chart image of a standard open.** A section `t`
of `𝒪_{Proj_S(A)}(n)` there satisfies `ψ(g^j) · t = ψ(x)`; both maps carry `ψ(g^j)` and `ψ(x)` to
the same sections by condition (1), and multiplication by `ψ_B(ψ(g^j))` is injective on the open of
`U(ψ)` over `D₊(g)`. -/
theorem MapsPsi.app_eq_of_basicOpen {θ₁ θ₂ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))} (h₁ : MapsPsi ψ θ₁) (h₂ : MapsPsi ψ θ₂) (V : S.Opens)
    (hV : IsAffineOpen V) {e : ℕ} {g : A.sectionRing V} (hg : g ∈ A.grading V e) (he : 0 < e)
    (n : ℤ) (t : Γ(Otw A n, (relativeProj A).chart V hV ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading V) g)) :
    (θ₁.app n).val.app (op (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) _ _ le_rfl t) =
      (θ₂.app n).val.app (op (relativeMapHom ψ ⁻¹ᵁ ((relativeProj A).chart V hV ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) _ _ le_rfl t) := by
  obtain ⟨j, N, x, hN, hH⟩ := exists_psiU_mul_eq V hV hg he n t
  have hW' := chart_image_le V hV (AlgebraicGeometry.Proj.basicOpen (A.grading V) g)
  have hOV := ((relativeMapHom ψ).preimage_mono hW').trans (relativeMapHom_preimage_toBase ψ V).le
  let aG := A.componentEquiv V (j * e) ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩
  let aX := A.componentEquiv V N x
  -- the value of either map on the product `ψ(g^j) · t`
  have stepA : ∀ θ, MapsPsi ψ θ →
      (θ.app (((j * e : ℕ) : ℤ) + n)).val.app (op (relativeMapHom ψ ⁻¹ᵁ
          ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A _) _ _ le_rfl
          (((twD A).algebra.mul ((j * e : ℕ) : ℤ) n).app
            (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
            ((relativeTwist A (j * e : ℕ)).val.map (homOfLE hW').op (psiU A (j * e) V aG)) t)) =
      ((Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
          (twistAlgebra B)).mul ((j * e : ℕ) : ℤ) n).app _
        (Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B (j * e : ℕ))
          ((relativeProj B).toBase ⁻¹ᵁ V) _ hOV (psiU B (j * e) V ((ψ.app _).app V aG)))
        ((θ.app n).val.app _
          (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) _ _
            le_rfl t)) := by
    intro θ hθ
    refine (congrArg ((θ.app (((j * e : ℕ) : ℤ) + n)).val.app _)
      (pullbackGradedAlgebra_mul_pullbackSection (relativeMapHom ψ) (twistAlgebra A) _ n _ _
        le_rfl _ t).symm).trans ?_
    refine (θ.map_mul _ n _ _ _).trans ?_
    exact congrArg (fun c => ((Stacks.RingedSpace.pullbackGradedAlgebra
      ψ.relativeMapDomain.ι.toLRSHom.toShHom (twistAlgebra B)).mul ((j * e : ℕ) : ℤ) n).app _ c
        ((θ.app n).val.app _
          (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) _ _ le_rfl t)))
      (MapsPsi.app_pullbackSection ψ hθ (j * e) V aG hW' hOV)
  have stepC : ∀ θ, MapsPsi ψ θ →
      HEq ((θ.app (((j * e : ℕ) : ℤ) + n)).val.app (op (relativeMapHom ψ ⁻¹ᵁ
          ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A _) _ _ le_rfl
          (((twD A).algebra.mul ((j * e : ℕ) : ℤ) n).app
            (op ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g))
            ((relativeTwist A (j * e : ℕ)).val.map (homOfLE hW').op (psiU A (j * e) V aG)) t)))
        (Scheme.Modules.pullbackSection ψ.relativeMapDomain.ι (relativeTwist B N)
          ((relativeProj B).toBase ⁻¹ᵁ V) _ hOV (psiU B N V ((ψ.app _).app V aX))) := by
    intro θ hθ
    refine (heq_apply_of_heq (fun k s => (θ.app k).val.app (op (relativeMapHom ψ ⁻¹ᵁ
        ((relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) g)))
        (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A k) _ _ le_rfl s))
      hN hH).trans (heq_of_eq ?_)
    exact MapsPsi.app_pullbackSection ψ hθ N V aX hW' hOV
  have keq := eq_of_heq ((heq_of_eq (stepA θ₁ h₁)).symm.trans ((stepC θ₁ h₁).trans
    ((stepC θ₂ h₂).symm.trans (heq_of_eq (stepA θ₂ h₂)))))
  have hb : DirectSum.of (B.sectionPieces V) (j * e) ((ψ.app ((j * e : ℕ) : ℤ)).app V aG) =
      ψ.sectionHom V g ^ j := by
    refine (ψ.sectionHom_of V aG).symm.trans ?_
    rw [show DirectSum.of (A.sectionPieces V) (j * e) aG = g ^ j from
      A.of_component V ⟨g ^ j, Stacks.MorphismToProj.HomogeneousRatios.pow_mem hg j⟩, map_pow]
  have hD : AlgebraicGeometry.Proj.basicOpen (B.grading V) (ψ.sectionHom V g) ≤
      AlgebraicGeometry.Proj.basicOpen (B.grading V)
        (DirectSum.of (B.sectionPieces V) (j * e) ((ψ.app ((j * e : ℕ) : ℤ)).app V aG)) := by
    rw [hb]
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hj, pow_zero, AlgebraicGeometry.Proj.basicOpen_one]
      exact le_top
    · rw [AlgebraicGeometry.Proj.basicOpen_pow _ _ _ hj]
  exact eq_of_mul_psiU_pullbackSection_eq ψ V hV (j * e) ((ψ.app _).app V aG) n
    ((ι_image_relativeMapHom_preimage_le ψ V hV hg he).trans (Scheme.Hom.image_mono _ hD)) hOV keq

/-- **Uniqueness: condition (1) and multiplicativity determine a map of graded algebras on the
twists over `U(ψ)`.** -/
theorem MapsPsi.eq {θ₁ θ₂ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))} (h₁ : MapsPsi ψ θ₁) (h₂ : MapsPsi ψ θ₂) : θ₁ = θ₂ := by
  refine SheafOfModules.GradedAlgebra.Hom.ext fun n => ?_
  refine Stacks.AlgebraicGeometry.ModuleLimits.hom_ext_of_pullbackSection (relativeMapHom ψ)
    fun O s => ?_
  let ι := {p : (Σ V : S.affineOpens, ℕ × A.sectionRing V.1) //
    p.2.2 ∈ A.grading p.1.1 p.2.1 ∧ 0 < p.2.1 ∧
      (relativeProj A).chart p.1.1 p.1.2 ''ᵁ
        AlgebraicGeometry.Proj.basicOpen (A.grading p.1.1) p.2.2 ≤ O}
  let Wk : ι → ψ.relativeMapDomain.toScheme.Opens := fun k => relativeMapHom ψ ⁻¹ᵁ
    ((relativeProj A).chart k.1.1.1 k.1.1.2 ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading k.1.1.1) k.1.2.2)
  have hk : ∀ k, Wk k ≤ relativeMapHom ψ ⁻¹ᵁ O := fun k =>
    (relativeMapHom ψ).preimage_mono k.2.2.2
  have hcov : relativeMapHom ψ ⁻¹ᵁ O ≤ ⨆ k, Wk k := by
    intro y hy
    obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
      (show (relativeProj A).toBase (relativeMapHom ψ y) ∈ (⊤ : S.Opens) from trivial)
    have hx : relativeMapHom ψ y ∈ (relativeProj A).chart V hV ''ᵁ ⊤ := by
      rwa [Stacks.AlgebraicGeometry.RelativeProjTwistGlue.chart_image_top]
    obtain ⟨z, -, hz⟩ := hx
    have hzO : z ∈ (relativeProj A).chart V hV ⁻¹ᵁ O := by
      show (relativeProj A).chart V hV z ∈ O
      rwa [show (relativeProj A).chart V hV z = relativeMapHom ψ y from hz]
    obtain ⟨d, f, hd, hf, hzf, hfO⟩ :=
      Stacks.AlgebraicGeometry.ProjShared.exists_basicOpen_homogeneous_le (A.grading V) hzO
    have hle : (relativeProj A).chart V hV ''ᵁ AlgebraicGeometry.Proj.basicOpen (A.grading V) f ≤
        O := (Scheme.Hom.image_mono _ hfO).trans (Scheme.Hom.image_preimage_le _ O)
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨⟨V, hV⟩, (d, f)⟩, hf, hd, hle⟩, ?_⟩
    exact ⟨z, hzf, hz⟩
  refine Stacks.AlgebraicGeometry.TwistMulLeg.eq_of_restrict_cover Wk hk hcov fun k => ?_
  have hW' : (relativeProj A).chart k.1.1.1 k.1.1.2 ''ᵁ
      AlgebraicGeometry.Proj.basicOpen (A.grading k.1.1.1) k.1.2.2 ≤ O := k.2.2.2
  have hres : ∀ θ : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B)),
      ((Scheme.Modules.pullback ψ.relativeMapDomain.ι).obj (relativeTwist B n)).presheaf.map
          (homOfLE (hk k)).op ((θ.app n).val.app (op (relativeMapHom ψ ⁻¹ᵁ O))
            (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) O _ le_rfl s)) =
        (θ.app n).val.app (op (Wk k))
          (Scheme.Modules.pullbackSection (relativeMapHom ψ) (relativeTwist A n) _ (Wk k) le_rfl
            ((relativeTwist A n).val.map (homOfLE hW').op s)) := by
    intro θ
    refine (PresheafOfModules.naturality_apply (θ.app n).val (homOfLE (hk k)).op _).symm.trans ?_
    refine congrArg ((θ.app n).val.app (op (Wk k))) ?_
    exact (Stacks.AlgebraicGeometry.ModuleLimits.pullbackSection_shrink _ _ _ _ _ le_rfl
      (hk k) (hk k) s).trans (pullbackSection_map _ _ hW' _ le_rfl s).symm
  refine (hres θ₁).trans (Eq.trans ?_ (hres θ₂).symm)
  exact MapsPsi.app_eq_of_basicOpen ψ h₁ h₂ k.1.1.1 k.1.1.2 k.2.1 k.2.2.1 n _

/-- **The map `θ` of Tag 07ZG is the only map of graded algebras with condition (1).** -/
theorem eq_relativeTwistAlgebraHom_of_mapsPsi {θ' : SheafOfModules.GradedAlgebra.Hom
      (Stacks.RingedSpace.pullbackGradedAlgebra (relativeMapHom ψ).toLRSHom.toShHom
        (twistAlgebra A))
      (Stacks.RingedSpace.pullbackGradedAlgebra ψ.relativeMapDomain.ι.toLRSHom.toShHom
        (twistAlgebra B))} (h : MapsPsi ψ θ') : θ' = relativeTwistAlgebraHom ψ :=
  MapsPsi.eq ψ h (mapsPsi_relativeTwistAlgebraHom ψ)

end Unique

end Stacks.AlgebraicGeometry.Tag07ZGTwist

end
