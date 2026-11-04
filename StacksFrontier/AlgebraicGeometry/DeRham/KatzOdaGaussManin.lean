module

public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaLocalWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.SmoothSpectralSequenceConcrete
public import StacksFrontier.AlgebraicGeometry.DeRham.KatzOdaConnection

/-!
# The Katz–Oda compatibility of the first differential of 0FMM, on a local form

Let `f : X ⟶ Y` be quasi-compact, quasi-separated and smooth over `g : Y ⟶ S`, with flat de Rham
cohomology sheaves. The remark [Stacks, Tag 0FMN] says that the first differential
`d_1 : Ω^p_{Y/S} ⊗ ℋ^q_dR(X/Y) ⟶ Ω^{p+1}_{Y/S} ⊗ ℋ^q_dR(X/Y)` obeys the Katz–Oda Leibniz rule
`d_1(ω ⊗ s) = dω ⊗ s + (-1)^p ω ∧ d_1(1 ⊗ s)`. The argument restricts to an open `U` carrying
`ω`, where left multiplication by `ρ(f⁻¹ω)` on `Ω^•_{X/S}|_{f⁻¹U}` is a cochain respecting the
filtration whose coboundary is left multiplication by `ρ(f⁻¹dω)`; the Leibniz rule of the
connecting morphisms (`CochainComplex.Filtered.shiftMap_actionGr_comp_derivedConnecting`) then
gives the rule, through the identification of the restricted first page.

## Main results

* `Stacks.Cohomology.HigherDirectImage.restrictedHigherDirectImageAction_eq` and
  `Stacks.Cohomology.HigherDirectImage.moduleRestriction_map_higherDirectImageGrConnecting`: the
  restricted action of a local morphism of complexes and the restricted connecting morphism, read
  on the restrictions of the complexes.
* `restrictedHigherDirectImageAction_actionGr_comp_higherDirectImageGrConnecting`: the Leibniz
  rule of the connecting morphisms, restricted to `U`.
* `Stacks.DeRhamSmooth.localTensorMap_comp_deRhamFirstPageFlatDifferential_of_wedgeStepSquare`:
  the Katz–Oda identity on `U` as an identity of morphisms, granted the step-square
  compatibilities, and its form on local sections.
* `Stacks.DeRhamSmooth.isKatzOdaLeibniz_of_wedgeStepSquare`: the Katz–Oda compatibility of
  `deRhamFirstPageFlatDifferential`, granted the step-square compatibilities.

## References

* [Stacks Project, Tag 0FMN](https://stacks.math.columbia.edu/tag/0FMN)
* N. Katz, T. Oda, *On the differentiation of de Rham cohomology classes with respect to
  parameters*, J. Math. Kyoto Univ. 8 (1968).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open RingedSpaceModuleAdjunction

universe u

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.Cohomology.HigherDirectImage

variable {X Y : RingedSpace.{u, u}} (φ : X ⟶ Y) (U : Opens Y)

/-- **The restricted higher direct images of a complex, read on the restriction of the
complex**: `(Rⁿφ_*K)|_U ≅ Hⁿ(R(φ|_V)_*(K|_V))`, `V = φ⁻¹U`, from
`derivedPushforwardHomologyRestrictIso` and the identification of the derived restriction of a
complex with the restriction of the complex. -/
def restrictedHomologyComplexIso (K : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (n : ℤ) :
    (moduleRestriction Y U).obj ((DerivedCategory.homologyFunctor _ n).obj
        ((totalDerivedPushforward φ).obj (DerivedCategory.Q.obj K))) ≅
      (DerivedCategory.homologyFunctor _ n).obj
        ((totalDerivedPushforward (restrictedMorphism φ U)).obj
          (DerivedCategory.Q.obj (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))) :=
  (derivedPushforwardHomologyRestrictIso φ U n).app (DerivedCategory.Q.obj K) ≪≫
    (DerivedCategory.homologyFunctor _ n).mapIso
      ((totalDerivedPushforward (restrictedMorphism φ U)).mapIso
        ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.app K))

/-- A morphism into a shift, conjugated by two morphisms, read on a shift sequence after a functor
commuting with the shift. -/
theorem shiftMap_map_comp_comp_shift {C D A : Type*} [Category C] [Category D] [Category A]
    [HasShift C ℤ] [HasShift D ℤ] (G : C ⥤ D) [G.CommShift ℤ] (H : D ⥤ A) [H.ShiftSequence ℤ]
    {X₁ X₂ Y₁ Y₂ : C} {s : ℤ} (x : X₁ ⟶ X₂) (y : X₂ ⟶ Y₁⟦s⟧) (z : Y₁ ⟶ Y₂) (n n' : ℤ)
    (h : s + n = n') :
    H.shiftMap (G.map (x ≫ y ≫ z⟦s⟧') ≫ (G.commShiftIso s).hom.app Y₂) n n' h =
      (H.shift n).map (G.map x) ≫ H.shiftMap (G.map y ≫ (G.commShiftIso s).hom.app Y₁) n n' h ≫
        (H.shift n').map (G.map z) := by
  have hn := (G.commShiftIso s).hom.naturality z
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hn,
    ← Category.assoc (G.map y), Functor.shiftMap_comp', Functor.shiftMap_comp]

/-- The restricted action of a morphism read through the factorisations of the derived restriction
is the shift map of its pushforward, conjugated by `restrictedHomologyComplexIso`. -/
private theorem restrictedDerivedAction_factors_eq
    {K₁ K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {s : ℤ}
    (ψ : DerivedCategory.Q.obj (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₁) ⟶
      (DerivedCategory.Q.obj (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₂))⟦s⟧) (n n' : ℤ) (h : s + n = n') :
    restrictedDerivedAction φ U
        ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom.app K₁ ≫ ψ ≫
          ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.inv.app K₂)⟦s⟧')
        n n' h =
      (restrictedHomologyComplexIso φ U K₁ n).hom ≫
        (DerivedCategory.homologyFunctor _ 0).shiftMap
          ((totalDerivedPushforward (restrictedMorphism φ U)).map ψ ≫
            ((totalDerivedPushforward (restrictedMorphism φ U)).commShiftIso s).hom.app _) n n'
          h ≫ (restrictedHomologyComplexIso φ U K₂ n').inv := by
  have e := shiftMap_map_comp_comp_shift (totalDerivedPushforward (restrictedMorphism φ U))
    (DerivedCategory.homologyFunctor _ 0)
    ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.hom.app K₁) ψ
    ((moduleRestriction X (preimageOpen φ U)).mapDerivedCategoryFactors.inv.app K₂) n n' h
  dsimp only [restrictedDerivedAction]
  refine (congrArg (fun t => (derivedPushforwardHomologyRestrictIso φ U n).hom.app _ ≫ t ≫
    (derivedPushforwardHomologyRestrictIso φ U n').inv.app (DerivedCategory.Q.obj K₂)) e).trans ?_
  simp only [restrictedHomologyComplexIso, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Category.assoc]
  rfl

/-- **The action of a local morphism of complexes, read on the restrictions of the complexes**:
`restrictedHigherDirectImageAction` of `u : K₁|_V ⟶ (K₂|_V)[p]` is the shift map of
`R(φ|_V)_*u`, conjugated by `restrictedHomologyComplexIso`. -/
theorem restrictedHigherDirectImageAction_eq
    {K₁ K₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ} {p : ℤ}
    (u' : ((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₁ ⟶
      (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K₂)⟦p⟧) (n n' : ℤ) (h : p + n = n') :
    restrictedHigherDirectImageAction φ U u' n n' h =
      (restrictedHomologyComplexIso φ U K₁ n).hom ≫
        (DerivedCategory.homologyFunctor _ 0).shiftMap
          (CochainComplex.Filtered.derivedShiftedMap
            (totalDerivedPushforward (restrictedMorphism φ U)) u') n n' h ≫
        (restrictedHomologyComplexIso φ U K₂ n').inv := by
  dsimp only [restrictedHigherDirectImageAction, CochainComplex.Filtered.derivedShiftedMap]
  simpa only [Category.assoc, Functor.commShiftIso_comp_hom_app, Functor.comp_map,
    Functor.map_comp] using restrictedDerivedAction_factors_eq φ U
    (DerivedCategory.Q.map u' ≫ (DerivedCategory.Q.commShiftIso p).hom.app _) n n' h

/-- **The restriction of the connecting morphism of the graded pieces, read on the restrictions
of the complexes**: the restriction to `U` of `R^nφ_*` of the connecting morphism
`gr^k ⟶ gr^{k+1}[1]` of a filtered complex is the connecting morphism of the restricted graded
pieces after `R(φ|_V)_*`, conjugated by `restrictedHomologyComplexIso`. -/
theorem moduleRestriction_map_higherDirectImageGrConnecting
    (M : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) (k n n' : ℤ)
    (h : n + 1 = n') :
    (moduleRestriction Y U).map
        (Stacks.Cohomology.FilteredComplex.higherDirectImageGrConnecting φ M k n n' h) =
      (restrictedHomologyComplexIso φ U ((FilteredObject.gr k).obj M) n).hom ≫
        (DerivedCategory.homologyFunctor _ 0).shiftMap
          (CochainComplex.Filtered.derivedConnecting (moduleRestriction X (preimageOpen φ U)) M
            (totalDerivedPushforward (restrictedMorphism φ U)) k) n n' (by omega) ≫
        (restrictedHomologyComplexIso φ U ((FilteredObject.gr (k + 1)).obj M) n').inv := by
  have hg := restrictedDerivedAction_global φ U
    (DerivedCategory.triangleOfSESδ (M.grShortComplex_shortExact k)) n n' (by omega)
  have hF := CochainComplex.Filtered.mapDerivedCategory_map_triangleOfSESδ
    (moduleRestriction X (preimageOpen φ U)) M k
  refine hg.symm.trans ((congrArg (restrictedDerivedAction φ U · n n' (by omega)) hF).trans ?_)
  exact restrictedDerivedAction_factors_eq φ U _ n n' _

/-- Conjugating a Leibniz identity by isomorphisms. -/
theorem conj_leibniz_paste {C : Type*} [Category C] [Preadditive C] {A₀ A₁ A₂ A₃ B₀ B₁ B₂ B₃ : C}
    (T₀ : A₀ ≅ B₀) (T₁ : A₁ ≅ B₁) (T₂ : A₂ ≅ B₂) (T₃ : A₃ ≅ B₃) {a : A₀ ⟶ A₁} {b : A₁ ⟶ A₂}
    {c : A₀ ⟶ A₂} {d : A₀ ⟶ A₃} {e : A₃ ⟶ A₂} {a' : B₀ ⟶ B₁} {b' : B₁ ⟶ B₂} {c' : B₀ ⟶ B₂}
    {d' : B₀ ⟶ B₃} {e' : B₃ ⟶ B₂} {ε : ℤˣ}
    (ha : a = T₀.hom ≫ a' ≫ T₁.inv) (hb : b = T₁.hom ≫ b' ≫ T₂.inv)
    (hc : c = T₀.hom ≫ c' ≫ T₂.inv) (hd : d = T₀.hom ≫ d' ≫ T₃.inv)
    (he : e = T₃.hom ≫ e' ≫ T₂.inv) (h : a' ≫ b' = c' + ε • (d' ≫ e')) :
    a ≫ b = c + ε • (d ≫ e) := by
  subst ha hb hc hd he
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a', h]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]

open CochainComplex.HomComplex in
/-- **The Leibniz rule of the connecting morphisms, restricted to `U`.** For a cochain `w` of
degree `p` on the restriction `K|_V` of a filtered complex `K`, respecting the filtration together
with its coboundary, the action of `μ_w^k` on the restricted higher direct images followed by the
restricted connecting morphism is `μ_{δw}^k + (-1)^p (μ_w^{k+1} ∘ δ_k)`. -/
theorem restrictedHigherDirectImageAction_actionGr_comp_higherDirectImageGrConnecting
    (M : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) {p : ℤ}
    {w : Cochain (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.X)
      (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.X) p}
    (hw : CochainComplex.Filtered.RespectsFiltration (moduleRestriction X (preimageOpen φ U)) M w)
    (hw' : CochainComplex.Filtered.RespectsFiltration (moduleRestriction X (preimageOpen φ U)) M
      (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') (n n₁ n₂ n₃ : ℤ) (h₁ : p + n = n₁)
    (h₂ : n₁ + 1 = n₂) (h₃ : n + 1 = n₃) (h₄ : p + n₃ = n₂) :
    restrictedHigherDirectImageAction φ U (CochainComplex.Filtered.actionGr hw hw' k k' hk)
          n n₁ h₁ ≫
        (moduleRestriction Y U).map
          (Stacks.Cohomology.FilteredComplex.higherDirectImageGrConnecting φ M k' n₁ n₂ h₂) =
      restrictedHigherDirectImageAction φ U
          (CochainComplex.Filtered.actionGr hw' CochainComplex.Filtered.respectsFiltration_δ_δ k
            (k' + 1) (by omega)) n n₂ (by omega) +
        p.negOnePow • ((moduleRestriction Y U).map
          (Stacks.Cohomology.FilteredComplex.higherDirectImageGrConnecting φ M k n n₃ h₃) ≫
          restrictedHigherDirectImageAction φ U
            (CochainComplex.Filtered.actionGr hw hw' (k + 1) (k' + 1) (by omega)) n₃ n₂ h₄) := by
  have := additive_totalDerivedPushforward (restrictedMorphism φ U)
  have hL := CochainComplex.Filtered.shiftMap_actionGr_comp_derivedConnecting
    (totalDerivedPushforward (restrictedMorphism φ U)) hw hw' k k' hk n n₁ n₂ n₃ h₁ (by omega)
    (by omega) h₄
  exact conj_leibniz_paste _ _ _ _ (restrictedHigherDirectImageAction_eq φ U _ n n₁ h₁)
    (moduleRestriction_map_higherDirectImageGrConnecting φ U M k' n₁ n₂ h₂)
    (restrictedHigherDirectImageAction_eq φ U _ n n₂ _)
    (moduleRestriction_map_higherDirectImageGrConnecting φ U M k n n₃ h₃)
    (restrictedHigherDirectImageAction_eq φ U _ n₃ n₂ h₄) hL

open CochainComplex.HomComplex in
/-- `restrictedHigherDirectImageAction_actionGr_comp_higherDirectImageGrConnecting`, with the
action of the coboundary replaced by an equal morphism. -/
theorem restrictedHigherDirectImageAction_actionGr_comp_higherDirectImageGrConnecting_of_eq
    (M : CochainComplex.Filtered (SheafOfModules.{u} (structureSheafRing X))) {p : ℤ}
    {w : Cochain (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.X)
      (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M.X) p}
    (hw : CochainComplex.Filtered.RespectsFiltration (moduleRestriction X (preimageOpen φ U)) M w)
    (hw' : CochainComplex.Filtered.RespectsFiltration (moduleRestriction X (preimageOpen φ U)) M
      (δ p (p + 1) w)) (k k' : ℤ) (hk : k + p = k') (n n₁ n₂ n₃ : ℤ) (h₁ : p + n = n₁)
    (h₂ : n₁ + 1 = n₂) (h₃ : n + 1 = n₃) (h₄ : p + n₃ = n₂)
    (μδ : ((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((FilteredObject.gr k).obj M) ⟶
      (((moduleRestriction X (preimageOpen φ U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj ((FilteredObject.gr (k' + 1)).obj M))⟦p + 1⟧)
    (hμδ : CochainComplex.Filtered.actionGr hw' CochainComplex.Filtered.respectsFiltration_δ_δ k
      (k' + 1) (by omega) = μδ) :
    restrictedHigherDirectImageAction φ U (CochainComplex.Filtered.actionGr hw hw' k k' hk)
          n n₁ h₁ ≫
        (moduleRestriction Y U).map
          (Stacks.Cohomology.FilteredComplex.higherDirectImageGrConnecting φ M k' n₁ n₂ h₂) =
      restrictedHigherDirectImageAction φ U μδ n n₂ (by omega) +
        p.negOnePow • ((moduleRestriction Y U).map
          (Stacks.Cohomology.FilteredComplex.higherDirectImageGrConnecting φ M k n n₃ h₃) ≫
          restrictedHigherDirectImageAction φ U
            (CochainComplex.Filtered.actionGr hw hw' (k + 1) (k' + 1) (by omega)) n₃ n₂ h₄) := by
  subst hμδ
  exact restrictedHigherDirectImageAction_actionGr_comp_higherDirectImageGrConnecting φ U M hw hw'
    k k' hk n n₁ n₂ n₃ h₁ h₂ h₃ h₄

end Stacks.Cohomology.HigherDirectImage

namespace Stacks.DeRhamSmooth

open Stacks.DeRhamDirectImage Stacks.Cohomology.HigherDirectImage CochainComplex.HomComplex

attribute [-instance] Stacks.Cohomology.SpectralLimit.hasSheafifyOpensMax

/-- Two morphisms of cochains respecting a filtration which are equal act equally on the graded
pieces. -/
theorem actionGr_congr {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    {F : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {M : CochainComplex.Filtered C} {p : ℤ}
    {w w' : Cochain ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.X)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.X) p} (h : w = w')
    (hw : CochainComplex.Filtered.RespectsFiltration F M w)
    (hw' : CochainComplex.Filtered.RespectsFiltration F M (δ p (p + 1) w))
    (hv : CochainComplex.Filtered.RespectsFiltration F M w')
    (hv' : CochainComplex.Filtered.RespectsFiltration F M (δ p (p + 1) w')) (k k' : ℤ)
    (hk : k + p = k') :
    CochainComplex.Filtered.actionGr hw hw' k k' hk =
      CochainComplex.Filtered.actionGr hv hv' k k' hk := by
  subst h
  rfl

/-- The pasting of the three identifications of the actions with the Leibniz rule. -/
theorem leibniz_flat_paste {C D : Type*} [Category C] [Category D] [Preadditive D] (F : C ⥤ D)
    {H₀ H₁ Hp Hp₁ E₀ E₁ Ep Ep₁ : C} (e₀ : H₀ ≅ E₀) (e₁ : H₁ ≅ E₁) (ep : Hp ≅ Ep)
    (ep₁ : Hp₁ ≅ Ep₁) {c₀ : H₀ ⟶ H₁} {cp : Hp ⟶ Hp₁} {m₀ : F.obj H₀ ⟶ F.obj Hp}
    {m₁ : F.obj H₁ ⟶ F.obj Hp₁} {mδ : F.obj H₀ ⟶ F.obj Hp₁} {L₀ : F.obj E₀ ⟶ F.obj Ep}
    {L₁ : F.obj E₁ ⟶ F.obj Ep₁} {Lδ : F.obj E₀ ⟶ F.obj Ep₁} {ε : ℤˣ}
    (g₀ : F.map e₀.inv ≫ m₀ ≫ F.map ep.hom = L₀) (g₁ : F.map e₁.inv ≫ m₁ ≫ F.map ep₁.hom = L₁)
    (gδ : F.map e₀.inv ≫ mδ ≫ F.map ep₁.hom = Lδ)
    (leib : m₀ ≫ F.map cp = mδ + ε • (F.map c₀ ≫ m₁)) :
    L₀ ≫ F.map (ep.inv ≫ cp ≫ ep₁.hom) =
      Lδ + ε • (F.map (e₀.inv ≫ c₀ ≫ e₁.hom) ≫ L₁) := by
  subst g₀ g₁ gδ
  have hp : F.map ep.hom ≫ F.map ep.inv = 𝟙 _ := by
    rw [← F.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  have h₁ : F.map e₁.hom ≫ F.map e₁.inv = 𝟙 _ := by
    rw [← F.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hp, reassoc_of% leib, reassoc_of% h₁]
  simp only [Preadditive.add_comp, Preadditive.comp_add, Linear.units_smul_comp,
    Linear.comp_units_smul, Category.assoc]

section Assembly

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]
  [Smooth f] (hflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf)
    (deRhamCohomologySheaf f q)) (U : Y.Opens)

/-- A sum of a morphism and a signed morphism, on a local section. -/
theorem add_units_smul_val_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M N : _root_.SheafOfModules.{u} R} (a b : M ⟶ N) (e : ℤˣ)
    (V : Cᵒᵖ) (x : M.val.obj V) :
    (a + e • b).val.app V x = a.val.app V x + (e : ℤ) • b.val.app V x := by
  rcases Int.units_eq_one_or e with rfl | rfl
  · simp
  · simp only [Units.val_neg, Units.val_one, neg_smul, one_smul, Units.neg_smul]
    rfl

/-- The image of a transport under a functor to sheaves of modules does not move local sections,
up to `HEq`. -/
theorem map_eqToHom_val_app_heq {C D : Type*} [Category C] [Category D]
    {J : GrothendieckTopology D} {R : Sheaf J RingCat.{u}} (F : C ⥤ _root_.SheafOfModules.{u} R)
    {A B : C} (e : A = B) (V : Dᵒᵖ) (x : (F.obj A).val.obj V) :
    (F.map (eqToHom e)).val.app V x ≍ x := by
  subst e
  simp

/-- Wedging with a local form, on the unit of `Ω^•_{Y/S}`, is the form, up to the name of its
degree. -/
theorem restrictedFormsWedge_app_one_heq (U : Opens Y.toRingedSpace) {p : ℤ}
    (ω : (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p).val.obj (op U)) (k' : ℤ)
    (h : p + 0 = k') (W : Opens ((Opens.toTopCat (Y.toRingedSpace : TopCat)).obj U)) :
    (restrictedFormsWedge g U ω 0 k' h).val.app (op W)
        ((AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).one.eval
          (op (openOfRestrict U W))) ≍
      (AlgebraicGeometry.Scheme.Hom.relativeDifferentialForms g p).val.map
        (homOfLE (openOfRestrict_le U W)).op ω := by
  have e1 : (restrictedFormsWedge g U ω 0 k' h).val.app (op W)
      ((AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).one.eval
        (op (openOfRestrict U W))) =
      ((moduleRestriction Y.toRingedSpace U).map (eqToHom (congrArg
        (AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).piece h))).val.app (op W)
        ((restrictedLeftMul U ((AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).mul
          p 0) ω).val.app (op W)
          ((AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).one.eval
            (op (openOfRestrict U W)))) := rfl
  refine (heq_of_eq e1).trans ((map_eqToHom_val_app_heq (moduleRestriction Y.toRingedSpace U)
    _ (op W) _).trans ?_)
  exact (AlgebraicGeometry.Scheme.Hom.relativeDifferentialFormsAlgebra g).mul_one p
    (op (openOfRestrict U W)) _

omit [QuasiCompact f] [QuasiSeparated f] [Smooth f] in
/-- The coboundary of left multiplication by `ρ(f⁻¹ω)` is left multiplication by `ρ(f⁻¹dω)`. -/
theorem δ_restrictedLeftMulCochain_pulledBackForm (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) :
    δ (p : ℤ) ((p : ℤ) + 1) (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g)
        (pulledBackForm f g U p ω)) =
      SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
        (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g)
        (pulledBackForm f g U (p + 1)
          (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω)) :=
  (SheafOfModules.DifferentialGradedAlgebra.δ_restrictedLeftMulCochain
    (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g)
    (pulledBackForm f g U p ω)).trans
    (congrArg (SheafOfModules.DifferentialGradedAlgebra.restrictedLeftMulCochain
      (X := inverseImageBase (f ≫ g)) (pulledBackOpen f g U) (deRhamDGA f g))
      (d_pulledBackForm f g U p ω))

include hflat in
/-- **The Katz–Oda identity on `U`, as an identity of morphisms**: for a `p`-form `ω` on `U`,
`(ω ∧ -) ∘ d_1 = (dω ∧ -) + (-1)^p d_1 ∘ (ω ∧ -)` on `(Ω^0 ⊗ ℋ^q)|_U`, granted the step-square
compatibilities of the actions of `ω` (at the cuts `0` and `1`) and of `dω` (at the cut `0`). -/
theorem localTensorMap_comp_deRhamFirstPageFlatDifferential_of_wedgeStepSquare (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (q : ℤ)
    (h₀ : WedgeStepSquare f g U p ω 0) (h₁ : WedgeStepSquare f g U p ω 1)
    (hd : WedgeStepSquare f g U (p + 1)
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) 0) :
    (localTensorMap f g U q (restrictedFormsWedge g U ω 0 (p : ℤ) (by simp)) ≫
        (moduleRestriction (inverseImageBase g) U).map
          (deRhamFirstPageFlatDifferential f g hflat (p : ℤ) q) :
        (moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g 0 q) ⟶
          (moduleRestriction (inverseImageBase g) U).obj
            (deRhamFirstPageFlat f g ((p : ℤ) + 1) q)) =
      @HAdd.hAdd ((moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g 0 q) ⟶
          (moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g ((p : ℤ) + 1) q))
        ((moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g 0 q) ⟶
          (moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g ((p : ℤ) + 1) q))
        ((moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g 0 q) ⟶
          (moduleRestriction (inverseImageBase g) U).obj (deRhamFirstPageFlat f g ((p : ℤ) + 1) q))
        instHAdd
        (localTensorMap f g U q (restrictedFormsWedge g U
          (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) 0 ((p : ℤ) + 1)
          (by push_cast; ring)))
        ((p : ℤ).negOnePow • ((moduleRestriction (inverseImageBase g) U).map
            (deRhamFirstPageFlatDifferential f g hflat 0 q) ≫
          localTensorMap f g U q
            (restrictedFormsWedge g U ω (0 + 1) ((p : ℤ) + 1) (by ring)))) := by
  have G₀ := restrictedHigherDirectImageAction_wedgeActionGr f g U hflat p ω q 0 h₀ 0 (p : ℤ)
    (by simp) (by simp) (by simp)
  have G₁ := restrictedHigherDirectImageAction_wedgeActionGr f g U hflat p ω q 1 h₁ (0 + 1)
    ((p : ℤ) + 1) (by simp) (by push_cast; ring) (by ring)
  have Gδ := restrictedHigherDirectImageAction_wedgeActionGr f g U hflat (p + 1)
    (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) q 0 hd 0 ((p : ℤ) + 1)
    (by simp) (by push_cast; ring) (by push_cast; ring)
  have hμ := actionGr_congr (δ_restrictedLeftMulCochain_pulledBackForm f g U p ω)
    (respectsFiltration_δ_restrictedLeftMulCochain f g U p ω)
    CochainComplex.Filtered.respectsFiltration_δ_δ
    (respectsFiltration_restrictedLeftMulCochain f g U (p + 1)
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω))
    (respectsFiltration_δ_restrictedLeftMulCochain f g U (p + 1)
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω)) 0 ((p : ℤ) + 1)
      (by ring)
  have L := restrictedHigherDirectImageAction_actionGr_comp_higherDirectImageGrConnecting_of_eq
    (relativeBase f g) U (deRhamSmoothFiltration f g : CochainComplex.Filtered
      (_root_.SheafOfModules.{u} (structureSheafRing (inverseImageBase (f ≫ g)))))
    (respectsFiltration_restrictedLeftMulCochain f g U p ω)
    (respectsFiltration_δ_restrictedLeftMulCochain f g U p ω) 0 (p : ℤ) (by simp) (0 + q)
    ((p : ℤ) + q) ((p : ℤ) + 1 + q) (0 + 1 + q) (by ring) (by ring) (by ring) (by ring) _ hμ
  exact leibniz_flat_paste (moduleRestriction (inverseImageBase g) U)
    (higherDirectImageGradedPieceFlatIso f g hflat 0 q)
    (higherDirectImageGradedPieceFlatIso f g hflat (0 + 1) q)
    (higherDirectImageGradedPieceFlatIso f g hflat (p : ℤ) q)
    (higherDirectImageGradedPieceFlatIso f g hflat ((p : ℤ) + 1) q) G₀ G₁ Gδ L

include hflat in
/-- **The Katz–Oda identity on local pure tensors over an open of `U`**, granted the step-square
compatibilities of the actions of `ω` and of `dω`. -/
theorem deRhamFirstPageFlatDifferential_app_formsTensorTmul_of_wedgeStepSquare (p : ℕ)
    (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (q : ℤ)
    (h₀ : WedgeStepSquare f g U p ω 0) (h₁ : WedgeStepSquare f g U p ω 1)
    (hd : WedgeStepSquare f g U (p + 1)
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) 0)
    (W : Opens ((Opens.toTopCat (Y.toRingedSpace : TopCat)).obj U))
    (s : (deRhamCohomologySheaf f q).val.obj (op (openOfRestrict U W))) :
    (Scheme.Hom.formsTensorSuccIso g (deRhamCohomologySheaf f q) p).hom.val.app
        (op (openOfRestrict U W))
      ((deRhamFirstPageFlatDifferential f g hflat (p : ℤ) q).val.app (op (openOfRestrict U W))
        (Scheme.Hom.formsTensorTmul g (deRhamCohomologySheaf f q) (p : ℤ) (op (openOfRestrict U W))
          ((Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map
            (homOfLE (openOfRestrict_le U W)).op ω) s)) =
      Scheme.Hom.formsTensorTmul g (deRhamCohomologySheaf f q) ((p + 1 : ℕ) : ℤ)
          (op (openOfRestrict U W))
          (Scheme.Hom.relativeDeRhamDifferentialSection g p (op (openOfRestrict U W))
            ((Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map
              (homOfLE (openOfRestrict_le U W)).op ω)) s +
        (-1 : ℤ) ^ p • (Scheme.Hom.formsTensorSuccIso g (deRhamCohomologySheaf f q) p).hom.val.app
          (op (openOfRestrict U W))
          (Scheme.Hom.formsTensorWedgeSection g (deRhamCohomologySheaf f q) p 1
          (op (openOfRestrict U W))
          ((Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map
            (homOfLE (openOfRestrict_le U W)).op ω)
          ((deRhamFirstPageFlatDifferential f g hflat 0 q).val.app (op (openOfRestrict U W))
            (Scheme.Hom.formsTensorUnitTmul g (deRhamCohomologySheaf f q) (op (openOfRestrict U W))
              s))) := by
  have D := congrArg (fun φ => φ.val.app (op W)
    (Scheme.Hom.formsTensorUnitTmul g (deRhamCohomologySheaf f q) (op (openOfRestrict U W)) s))
    (localTensorMap_comp_deRhamFirstPageFlatDifferential_of_wedgeStepSquare f g hflat U p ω q h₀ h₁
      hd)
  have l₀ := (localTensorMap_app_tmul f g U q (restrictedFormsWedge g U ω 0 (p : ℤ) (by simp))
      (op W) _ s).trans (congrArg (fun t => Scheme.Hom.formsTensorTmul g (deRhamCohomologySheaf f q)
        (p : ℤ) (op (openOfRestrict U W)) t s)
      (eq_of_heq (restrictedFormsWedge_app_one_heq g U ω (p : ℤ) (by simp) W)))
  have ld := localTensorMap_app_tmul f g U q (restrictedFormsWedge g U
    (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) 0 ((p : ℤ) + 1)
    (by push_cast; ring)) (op W)
    ((Scheme.Hom.relativeDifferentialFormsAlgebra g).one.eval (op (openOfRestrict U W))) s
  have hd₁ := PresheafOfModules.naturality_apply ((Scheme.Hom.deRhamComplex g).d p (p + 1)).val
      (homOfLE (openOfRestrict_le U W)).op ω
  have hA := Scheme.Hom.formsTensorTmul_heq g (deRhamCohomologySheaf f q)
    (show (p : ℤ) + 1 = ((p + 1 : ℕ) : ℤ) by push_cast; ring) (op (openOfRestrict U W)) _ _
    ((restrictedFormsWedge_app_one_heq g U
      (((Scheme.Hom.deRhamComplex g).d p (p + 1)).val.app (op U) ω) ((p : ℤ) + 1)
      (by push_cast; ring) W).trans (heq_of_eq hd₁.symm)) s
  have lw := congrArg (fun φ => φ.val.app (op W)
    ((deRhamFirstPageFlatDifferential f g hflat 0 q).val.app (op (openOfRestrict U W))
      (Scheme.Hom.formsTensorUnitTmul g (deRhamCohomologySheaf f q) (op (openOfRestrict U W)) s)))
    (localTensorMap_restrictedFormsWedge f g U q ω (0 + 1))
  refine (congrArg (fun t => (deRhamFirstPageFlatDifferential f g hflat (p : ℤ) q).val.app
    (op (openOfRestrict U W)) t) l₀).symm.trans ?_
  refine D.trans ((add_units_smul_val_app _ _ _ _ _).trans ?_)
  rw [Int.coe_negOnePow_natCast]
  exact congrArg₂ (· + ·) (ld.trans (eq_of_heq hA)) (congrArg (fun t => (-1 : ℤ) ^ p • t) lw)

include hflat in
/-- **The Katz–Oda compatibility of the first differential, granted the step-square
compatibilities of the actions of all local forms.** -/
theorem isKatzOdaLeibniz_of_wedgeStepSquare (q : ℤ)
    (hμ : ∀ (U : Y.Opens) (p : ℕ) (ω : ((Scheme.Hom.deRhamComplex g).X p).val.obj (op U)) (k : ℕ),
      WedgeStepSquare f g U p ω k) :
    Scheme.Hom.IsKatzOdaLeibniz g (deRhamCohomologySheaf f q)
      (fun p => deRhamFirstPageFlatDifferential f g hflat p q) := by
  intro p U ω s
  have key : ∀ (V : Y.Opens) (hV : V ≤ U.unop) (s : (deRhamCohomologySheaf f q).val.obj (op V)),
      (Scheme.Hom.formsTensorSuccIso g (deRhamCohomologySheaf f q) p).hom.val.app (op V)
        ((deRhamFirstPageFlatDifferential f g hflat (p : ℤ) q).val.app (op V)
          (Scheme.Hom.formsTensorTmul g (deRhamCohomologySheaf f q) (p : ℤ) (op V)
            ((Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map (homOfLE hV).op ω) s)) =
      Scheme.Hom.formsTensorTmul g (deRhamCohomologySheaf f q) ((p + 1 : ℕ) : ℤ) (op V)
          (Scheme.Hom.relativeDeRhamDifferentialSection g p (op V)
            ((Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map (homOfLE hV).op ω)) s +
        (-1 : ℤ) ^ p • (Scheme.Hom.formsTensorSuccIso g (deRhamCohomologySheaf f q) p).hom.val.app
          (op V)
          (Scheme.Hom.formsTensorWedgeSection g (deRhamCohomologySheaf f q) p 1 (op V)
          ((Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map (homOfLE hV).op ω)
          ((deRhamFirstPageFlatDifferential f g hflat 0 q).val.app (op V)
            (Scheme.Hom.formsTensorUnitTmul g (deRhamCohomologySheaf f q) (op V) s))) := by
    intro V hV s
    obtain ⟨W, rfl⟩ := exists_openOfRestrict_eq (Xr := Y.toRingedSpace) U.unop hV
    exact deRhamFirstPageFlatDifferential_app_formsTensorTmul_of_wedgeStepSquare f g hflat U.unop
      p ω q (hμ _ p ω 0) (hμ _ p ω 1) (hμ _ (p + 1) _ 0) W s
  have hω : (Scheme.Hom.relativeDifferentialForms g (p : ℤ)).val.map
      (homOfLE (le_refl U.unop)).op ω = ω := by
    rw [show (homOfLE (le_refl U.unop)).op = 𝟙 (op U.unop) from rfl]
    simp only [PresheafOfModules.map_id]
    rfl
  have := key U.unop (le_refl _) s
  rw [hω] at this
  exact this

end Assembly

end Stacks.DeRhamSmooth
