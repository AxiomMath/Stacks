module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.AffineDerivedSectionsBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteFlatCovers
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.RepresentableQC.ChartCovers
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryCompIsoOnHomotopyCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EvaluationRestrictionHomotopySquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.QuasiCoherentCohomologyUnderFlatRestrictions
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived base change property of Stacks 0H15 is local for the étale topology

Let `𝒳` be an algebraic stack and `K` an object of `D(𝒪_𝒳)` (module universe `u + 1`) whose
cohomology sheaves lie in `LQCoh^fbc(𝒪_𝒳)`. For a morphism `a : x ⟶ x'` of `𝒳_{affine}` write
`c_a : RΓ(x', K) ⊗^L_{𝒪(x')} 𝒪(x) ⟶ RΓ(x, K)` for the map of Stacks 0H15
(`AlgebraicGeometry.Stack.FlatFppf.derivedSectionsBaseChange`). This file proves the second
paragraph of the proof of Stacks 0H15: whether `c_a` is invertible is local on `x'` for the
étale topology — indeed for any of the five topologies of `𝒳_{affine}`, the fppf one included.

Let `{x'_i ⟶ x'}` be a covering and `x_i = x ×_{x'} x'_i`. The source argues that
`𝒪(x') ⟶ ∏ 𝒪(x'_i)` is faithfully flat with `∏ 𝒪(x_i) = 𝒪(x) ⊗_{𝒪(x')} ∏ 𝒪(x'_i)`, and that "a
simple algebra argument we omit" reduces the invertibility of `c_a` to that of the `c_{a_i}` for
`a_i : x_i ⟶ x'_i`. The argument formalized here is:

* **Transitivity** (`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedSectionsBaseChange_comp_iff`).
  For `u : z ⟶ y` and `v : y ⟶ w` with `c_u` invertible, `c_{u ≫ v}` is invertible exactly when
  `c_v ⊗^L_{𝒪(y)} 𝒪(z)` is. This rests on the compatibility of the derived restriction maps with
  composition (`Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict_comp_app`), proved on
  the homotopy category where restriction is termwise, and on the formal behaviour of adjoint
  transposes under composition of adjunctions
  (`CategoryTheory.Adjunction.isIso_homEquiv_symm_iff_of_comp`).
* **Faithfully flat descent of isomorphisms of `D(A)`**
  (`Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange.isIso_of_isIso_dBaseChange_map`):
  along a finite family of flat ring maps `A ⟶ A_i` with `A ⟶ ∏ A_i` faithfully flat, a morphism
  of `D(A)` is invertible as soon as all its derived base changes are. Flat base change commutes
  with cohomology, and faithfully flat base change detects isomorphisms of modules.
* **The geometric step**
  (`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedSectionsBaseChange_of_covering`). Refine the
  covering to a finite flat covering `y_k ⟶ x'` (Stacks 0H0A) and set `P_k = x ×_{x'} y_k` in
  `𝒳_{affine}`. The maps `P_k ⟶ x` are flat and jointly surjective, so
  `𝒪(x) ⟶ ∏ 𝒪(P_k)` is faithfully flat. Along the flat maps `P_k ⟶ x` and `y_k ⟶ x'` the maps of
  Stacks 0H15 are invertible (the flat case of Stacks 0H15,
  `AlgebraicGeometry.Stack.FlatFppf.isIso_derivedSectionsBaseChange_of_flat`), and along
  `P_k ⟶ y_k` by hypothesis; transitivity applied to `P_k ⟶ y_k ⟶ x'` and `P_k ⟶ x ⟶ x'` makes
  `c_a ⊗^L 𝒪(P_k)` invertible for every `k`, and descent concludes.

## Main results

* `AlgebraicGeometry.Stack.FlatFppf.isIso_derivedSectionsBaseChange_of_covering`: if the maps of
  Stacks 0H15 are invertible along every arrow into a member of a covering sieve of `x'`, then
  along every arrow `x ⟶ x'`.
* `AlgebraicGeometry.Stack.FlatFppf.hasAffineDerivedSectionsBaseChange_of_covering`: if every
  object of `𝒳_{affine}` has such a covering sieve, `K` has the derived base change property of
  Stacks 0H15.

No `@[stacks]` attribute is claimed: this is a step of the proof of Stacks 0H15.

## References

* [Stacks Project, Tag 0H15](https://stacks.math.columbia.edu/tag/0H15)
* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.ModulesOnACategory.ChaoticComparison.sheafOfModules_hasDerivedCategory
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteLimits
  Stacks.ModulesOnACategory.QuasiCoherentEquivalence.rsPreservesFiniteColimits

/-! ### Adjoint transposes along a composite of adjunctions -/

namespace CategoryTheory.Adjunction

variable {C₁ C₂ C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂} {L₁₂ : C₁ ⥤ C₃} {R₁₂ : C₃ ⥤ C₁}

/-- **Two out of three for adjoint transposes along a composite.** Let `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and
`L₁₂ ⊣ R₁₂` be adjunctions with `R₁₂ ≅ R₂ ⋙ R₁`, and let `f₁ : X ⟶ R₁ Y`, `f₂ : Y ⟶ R₂ Z` and
`f₁₂ : X ⟶ R₁₂ Z` be compatible: `f₁₂` followed by the isomorphism is `f₁ ≫ R₁ f₂`. If the
transpose `L₂ Y ⟶ Z` of `f₂` is invertible, the transpose `L₁₂ X ⟶ Z` of `f₁₂` is invertible
exactly when `L₂` of the transpose `L₁ X ⟶ Y` of `f₁` is: up to the canonical isomorphism
`L₁₂ ≅ L₁ ⋙ L₂`, the first is `L₂(f₁^♭) ≫ f₂^♭`. -/
theorem isIso_homEquiv_symm_iff_of_comp (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁₂ : L₁₂ ⊣ R₁₂)
    (e : R₁₂ ≅ R₂ ⋙ R₁) {X : C₁} {Y : C₂} {Z : C₃} (f₁ : X ⟶ R₁.obj Y) (f₂ : Y ⟶ R₂.obj Z)
    (f₁₂ : X ⟶ R₁₂.obj Z) (h : f₁₂ ≫ e.hom.app Z = f₁ ≫ R₁.map f₂)
    (h₂ : IsIso ((adj₂.homEquiv Y Z).symm f₂)) :
    IsIso ((adj₁₂.homEquiv X Z).symm f₁₂) ↔ IsIso (L₂.map ((adj₁.homEquiv X Y).symm f₁)) := by
  have key : (((adj₁.comp adj₂).ofNatIsoRight e.symm).homEquiv X Z).symm f₁₂ =
      L₂.map ((adj₁.homEquiv X Y).symm f₁) ≫ (adj₂.homEquiv Y Z).symm f₂ := by
    rw [homEquiv_ofNatIsoRight_symm_apply, comp_homEquiv]
    simp only [Iso.symm_inv, Equiv.symm_trans_apply]
    rw [h, homEquiv_naturality_right_symm, homEquiv_naturality_left_symm]
  rw [Stacks.ModulesOnACategory.QuasiCoherentCohomology.isIso_homEquiv_symm_iff adj₁₂
    ((adj₁.comp adj₂).ofNatIsoRight e.symm) f₁₂, key]
  exact isIso_comp_right_iff _ _

end CategoryTheory.Adjunction

/-! ### Faithfully flat descent of isomorphisms -/

universe uA uB m

/-- **Extension of scalars along a finite family of flat ring maps whose product is faithfully
flat detects isomorphisms**: a map of modules whose base changes along all the `φ i` are
invertible is invertible. Its kernel and cokernel have vanishing base changes, flat base change
being exact. -/
@[ega "IV 2.2.7" "partial",
  ega "IV 2.5.8.7" "more general",
  sga "4½ Arcata 1.4.2" "Clause (i), special case"]
theorem ModuleCat.isIso_of_isIso_extendScalars_of_faithfullyFlat_pi {A : Type uA} [CommRing A]
    {ι : Type*} [Finite ι] {B : ι → Type uB} [∀ i, CommRing (B i)] (φ : ∀ i, A →+* B i)
    (hφ : ∀ i, (φ i).Flat) (h : (RingHom.pi φ).FaithfullyFlat) {M N : ModuleCat.{max uB m} A}
    (f : M ⟶ N) (hf : ∀ i, IsIso ((ModuleCat.extendScalars (φ i)).map f)) : IsIso f := by
  have hk : IsZero (kernel f) := by
    refine ModuleCat.isZero_of_isZero_extendScalars_of_faithfullyFlat_pi φ h _ fun i => ?_
    have := ModuleCat.extendScalars_preservesFiniteLimits_of_flat (φ i) (hφ i)
    exact (isZero_kernel_of_mono ((ModuleCat.extendScalars (φ i)).map f)).of_iso
      (PreservesKernel.iso (ModuleCat.extendScalars (φ i)) f)
  have hc : IsZero (cokernel f) :=
    ModuleCat.isZero_of_isZero_extendScalars_of_faithfullyFlat_pi φ h _ fun i =>
      (isZero_cokernel_of_epi ((ModuleCat.extendScalars (φ i)).map f)).of_iso
      (PreservesCokernel.iso (ModuleCat.extendScalars (φ i)) f)
  have := Preadditive.mono_of_isZero_kernel f hk
  have := Preadditive.epi_of_isZero_cokernel f hc
  exact isIso_of_mono_of_epi f

namespace Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

open Stacks.ModulesOnACategory.CartesianObjects (commRingOfComm)

universe r t

attribute [local instance] HasDerivedCategory.standard

/-- **Faithfully flat descent of isomorphisms of `D(R)`.** Let `ψ i : R ⟶ A i` be a finite family
of flat ring maps whose product `R ⟶ ∏ A i` is faithfully flat. A morphism of `D(R)` whose derived
base changes `- ⊗^L_R A i` are all invertible is invertible: on cohomology, flat base change
commutes with `H^q`, and faithfully flat base change detects isomorphisms of modules. -/
@[ega "IV 2.2.7" "special case", sga "4½ Arcata 1.4.2" "more general"]
theorem isIso_of_isIso_dBaseChange_map {R : RingCat.{r}} (hR : ∀ x y : R, x * y = y * x)
    {ι : Type*} [Finite ι] {A : ι → RingCat.{r}} (hA : ∀ i, ∀ x y : A i, x * y = y * x)
    (ψ : ∀ i, R ⟶ A i)
    (hψ : ∀ i, letI := commRingOfComm R hR; letI := commRingOfComm (A i) (hA i); (ψ i).hom.Flat)
    (hff : letI := commRingOfComm R hR; letI : ∀ i, CommRing (A i) :=
      (fun i => commRingOfComm (A i) (hA i)); (RingHom.pi fun i => (ψ i).hom).FaithfullyFlat)
    {M N : DerivedCategory (ModuleCat.{max t r} R)} (φ : M ⟶ N)
    (h : ∀ i, IsIso ((dBaseChange.{r, t} (ψ i) hR (hA i)).map φ)) : IsIso φ := by
  let := commRingOfComm R hR
  let : ∀ i, CommRing (A i) := fun i => commRingOfComm (A i) (hA i)
  rw [DerivedCategory.isIso_iff]
  intro q
  refine ModuleCat.isIso_of_isIso_extendScalars_of_faithfullyFlat_pi (fun i => (ψ i).hom) hψ hff
    _ fun i => ?_
  have := isIso_baseChangeHomologyComparison_of_flat.{r, t} (ψ i) hR (hA i) (hψ i) M q
  have := isIso_baseChangeHomologyComparison_of_flat.{r, t} (ψ i) hR (hA i) (hψ i) N q
  have hn := baseChangeHomologyComparison_naturality.{r, t} (ψ i) hR (hA i) φ q
  have : IsIso ((ModuleCat.extendScalars.{r, r, max t r} (ψ i).hom).map
      ((DerivedCategory.homologyFunctor _ q).map φ) ≫
        baseChangeHomologyComparison.{r, t} (ψ i) hR (hA i) N q) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (baseChangeHomologyComparison.{r, t} (ψ i) hR (hA i) N q)

end Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

/-! ### Derived restriction along a composite -/

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] restrictScalars_preservesFiniteLimits
  restrictScalars_preservesFiniteColimits evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})

/-- Restriction of sections along a composite, termwise: restricting along `u ≫ v` is restricting
along `v` and then along `u`. -/
theorem sectionsRestrict_comp_app {U V W : C} (u : U ⟶ V) (v : V ⟶ W)
    (M : SheafOfModules.{wModule} O) :
    (sectionsRestrict O (u ≫ v)).app M ≫
        (ModuleCat.restrictScalarsComp'.{wModule} (O.obj.map v.op).hom
          (O.obj.map u.op).hom (O.obj.map (u ≫ v).op).hom
          (by rw [op_comp, Functor.map_comp, RingCat.hom_comp])).symm.inv.app _ =
      (sectionsRestrict O v).app M ≫
        (ModuleCat.restrictScalars (O.obj.map v.op).hom).map ((sectionsRestrict O u).app M) := by
  ext m
  change M.val.map (u ≫ v).op m = M.val.map u.op (M.val.map v.op m)
  rw [op_comp, PresheafOfModules.map_comp]
  rfl

variable [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-- A diagram chase, stated with every object and morphism a variable so that it applies by
`exact` where the objects agree only up to unfolding. -/
private theorem comp_chase {D D' : Type*} [Category* D] [Category* D'] (G : D' ⥤ D)
    {x₀ x₁ x₂ x₃ y₁ : D} {z₁ z₂ z₃ : D'}
    (A₁ : x₀ ⟶ x₁) (i₁ : x₁ ⟶ x₁) (B₁ : x₁ ⟶ x₂) (B₁' : x₂ ⟶ x₁) (C₁ : x₁ ⟶ x₃)
    (D₁ : x₃ ⟶ G.obj z₂) (A₂ : x₀ ⟶ y₁) (i₂ : y₁ ⟶ y₁) (B₂ : y₁ ⟶ G.obj z₁) (A₃ : z₁ ⟶ z₂)
    (i₃ : z₂ ⟶ z₂) (B₃ : z₂ ⟶ z₃) (N : y₁ ⟶ x₃)
    (hi₁ : i₁ = 𝟙 _) (hB : B₁ ≫ B₁' = 𝟙 _) (hi₂ : i₂ = 𝟙 _) (hi₃ : i₃ = 𝟙 _)
    (hn : B₂ ≫ G.map A₃ = N ≫ D₁) (hc : A₁ ≫ C₁ = A₂ ≫ N) :
    (A₁ ≫ i₁ ≫ B₁) ≫ (B₁' ≫ C₁ ≫ D₁ ≫ G.map B₃) = (A₂ ≫ i₂ ≫ B₂) ≫ G.map (A₃ ≫ i₃ ≫ B₃) := by
  subst hi₁ hi₂ hi₃
  simp only [Category.id_comp, Category.assoc, G.map_comp]
  rw [reassoc_of% hB, reassoc_of% hc, reassoc_of% hn]

omit [HasSheafify J AddCommGrpCat.{wModule}] [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)] in
/-- **Restriction on the homotopy category along a composite.** The termwise restriction of
complexes of sections along `u ≫ v`, followed by the composition isomorphism of derived
restrictions of scalars, is the termwise restriction along `v` followed by the derived
restriction of scalars of the termwise restriction along `u`. -/
theorem homotopySectionsRestrict_comp_app {U V W : C} (u : U ⟶ V) (v : V ⟶ W)
    (X : HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) :
    (homotopySectionsRestrict O (u ≫ v)).app X ≫
        (Functor.mapDerivedCategoryCompIsoOfCompIso
          (ModuleCat.restrictScalarsComp'.{wModule} (O.obj.map v.op).hom
            (O.obj.map u.op).hom (O.obj.map (u ≫ v).op).hom
            (by rw [op_comp, Functor.map_comp, RingCat.hom_comp])).symm).inv.app
          ((homotopySections.{u, v, wRing, wModule} O U).obj X) =
      (homotopySectionsRestrict O v).app X ≫
        (restrictScalarsDerived O v).map ((homotopySectionsRestrict O u).app X) := by
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  let e := (ModuleCat.restrictScalarsComp'.{wModule} (O.obj.map v.op).hom
    (O.obj.map u.op).hom (O.obj.map (u ≫ v).op).hom
    (by rw [op_comp, Functor.map_comp, RingCat.hom_comp])).symm
  let Fv := ModuleCat.restrictScalars.{wModule} (O.obj.map v.op).hom
  let Fuv := ModuleCat.restrictScalars.{wModule} (O.obj.map (u ≫ v).op).hom
  let q := fun (R : RingCat.{wRing}) =>
    HomotopyCategory.quotient (ModuleCat.{wModule} R) (ComplexShape.up ℤ)
  let J := (q _).obj (((_root_.SheafOfModules.evaluation O (op U)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj I)
  have hci := Functor.mapDerivedCategoryCompIso_inv_app_Qh e J
  -- the termwise restrictions, on complexes
  have h₁ : (NatTrans.mapHomologicalComplex (sectionsRestrict O (u ≫ v))
        (ComplexShape.up ℤ)).app I ≫
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app
          (((_root_.SheafOfModules.evaluation O (op U)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I) =
      (NatTrans.mapHomologicalComplex (sectionsRestrict O v) (ComplexShape.up ℤ)).app I ≫
        (Fv.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (sectionsRestrict O u) (ComplexShape.up ℤ)).app I) :=
    HomologicalComplex.hom_ext _ _ fun n => sectionsRestrict_comp_app O u v (I.X n)
  -- on the homotopy category
  have h₀ : (q _).map ((NatTrans.mapHomologicalComplex
        (sectionsRestrict O (u ≫ v)) (ComplexShape.up ℤ)).app I) ≫
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app J =
      (q _).map ((NatTrans.mapHomologicalComplex (sectionsRestrict O v)
          (ComplexShape.up ℤ)).app I) ≫
        (Fv.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((q _).map ((NatTrans.mapHomologicalComplex
            (sectionsRestrict O u) (ComplexShape.up ℤ)).app I)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg (q _).map h₁).trans (Functor.map_comp _ _ _))
  have hc := (Functor.map_comp DerivedCategory.Qh _ _).symm.trans
    ((congrArg DerivedCategory.Qh.map h₀).trans (Functor.map_comp _ _ _))
  have hn := Fv.mapDerivedCategoryFactorsh.inv.naturality
    ((q _).map ((NatTrans.mapHomologicalComplex (sectionsRestrict O u) (ComplexShape.up ℤ)).app I))
  exact (congrArg (fun t => (homotopySectionsRestrict O (u ≫ v)).app ((HomotopyCategory.quotient
    (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)).obj I) ≫ t) hci).trans
    (comp_chase (restrictScalarsDerived O v) _ _ _ _ _ _ _ _ _ _ _ _ _
      (CategoryTheory.Functor.map_id _ _) (Fuv.mapDerivedCategoryFactorsh.inv_hom_id_app J)
      (CategoryTheory.Functor.map_id _ _) (CategoryTheory.Functor.map_id _ _) hn.symm hc)

/-- A second diagram chase, stated with every object and morphism a variable. -/
private theorem comp_chase₂ {D D' : Type*} [Category* D] [Category* D'] (G : D' ⥤ D)
    {a b c m : D} {p₁ p₂ p₃ p₄ : D'}
    (e : a ⟶ b) (d : b ⟶ c) (ci : c ⟶ G.obj p₄) (h : a ⟶ m) (rU : m ⟶ c)
    (h1 : e ≫ d = h ≫ rU) (ci' : m ⟶ G.obj p₃) (s : p₃ ⟶ p₄)
    (hnat : rU ≫ ci = ci' ≫ G.map s) (hv : a ⟶ G.obj p₁) (hu : p₁ ⟶ p₃)
    (hstar : h ≫ ci' = hv ≫ G.map hu) (dv : b ⟶ G.obj p₂) (uV : p₁ ⟶ p₂)
    (h2 : e ≫ dv = hv ≫ G.map uV) (du : p₂ ⟶ p₄) (h3 : uV ≫ du = hu ≫ s) :
    e ≫ d ≫ ci = e ≫ dv ≫ G.map du := by
  rw [reassoc_of% h1, hnat, reassoc_of% hstar, reassoc_of% h2, ← G.map_comp, ← G.map_comp, h3]

/-- **Derived restriction along a composite.** For `u : U ⟶ V` and `v : V ⟶ W`, the derived
restriction `RΓ(W, K) ⟶ RΓ(U, K)` along `u ≫ v`, read through the composition isomorphism of
derived restrictions of scalars, is the derived restriction along `v` followed by the derived
restriction of scalars of the derived restriction along `u`. -/
theorem derivedSectionsRestrict_comp_app {U V W : C} (u : U ⟶ V) (v : V ⟶ W)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (derivedSectionsRestrict O (u ≫ v)).app K ≫
        (Functor.mapDerivedCategoryCompIsoOfCompIso
          (ModuleCat.restrictScalarsComp'.{wModule} (O.obj.map v.op).hom
            (O.obj.map u.op).hom (O.obj.map (u ≫ v).op).hom
            (by rw [op_comp, Functor.map_comp, RingCat.hom_comp])).symm).inv.app
          ((derivedSections.{u, v, wRing, wModule, g} O U).obj K) =
      (derivedSectionsRestrict O v).app K ≫
        (restrictScalarsDerived O v).map ((derivedSectionsRestrict O u).app K) := by
  -- the characterizing equation of the derived restriction, at an object of the homotopy category
  have hfac : ∀ {A B : C} (g : A ⟶ B)
      (X : HomotopyCategory (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)),
      ((homotopySections.{u, v, wRing, wModule} O B).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))).app X ≫
        (derivedSectionsRestrict.{u, v, wRing, wModule, g} O g).app (DerivedCategory.Qh.obj X) =
      (homotopySectionsRestrict O g).app X ≫ (restrictScalarsDerived O g).map
        (((homotopySections.{u, v, wRing, wModule} O A).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ))).app X) := by
    intro A B g X
    have h := congrArg (fun τ => NatTrans.app τ X) (derivedSectionsRestrict_fac O g)
    rwa [sectionsRestrictUnit_eq] at h
  let e := (ModuleCat.restrictScalarsComp'.{wModule} (O.obj.map v.op).hom
    (O.obj.map u.op).hom (O.obj.map (u ≫ v).op).hom
    (by rw [op_comp, Functor.map_comp, RingCat.hom_comp])).symm
  have key : derivedSectionsRestrict O (u ≫ v) ≫
      Functor.whiskerLeft (derivedSections O U) (Functor.mapDerivedCategoryCompIsoOfCompIso e).inv =
      (derivedSectionsRestrict O v ≫ Functor.whiskerRight (derivedSectionsRestrict O u)
        (restrictScalarsDerived O v) : derivedSections O W ⟶ derivedSections O U ⋙
          ((ModuleCat.restrictScalars.{wModule} (O.obj.map u.op).hom).mapDerivedCategory ⋙
            (ModuleCat.restrictScalars.{wModule} (O.obj.map v.op).hom).mapDerivedCategory)) := by
    refine derivedSectionsRestrict_ext O _ _ ?_
    ext X
    exact comp_chase₂ (restrictScalarsDerived O v) _ _ _ _ _ (hfac (u ≫ v) X) _ _
      ((Functor.mapDerivedCategoryCompIsoOfCompIso e).inv.naturality _)
      _ _ (homotopySectionsRestrict_comp_app O u v X) _ _ (hfac v X) _ (hfac u X)
  exact congrArg (fun τ => NatTrans.app τ K) key

end Stacks.Cohomology.HypercohomologyEdge

/-! ### Étale locality of the map of Stacks 0H15 -/

namespace AlgebraicGeometry.Stack.FlatFppf

open Stacks.Cohomology.HypercohomologyEdge
open Stacks.ModulesOnACategory.PullbackQuasiCoherentBaseChange

universe u w

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasSheafify_fppfTopology_largeSections
  wEqualsLocallyBijective_fppfTopology_largeSections
attribute [local instance] isGrothendieckAbelian_ambientModulesSucc

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Transitivity of the map of Stacks 0H15.** For `a : z ⟶ y` and `b : y ⟶ w` in `𝒳` such that
`RΓ(y, K) ⊗^L_{𝒪(y)} 𝒪(z) ⟶ RΓ(z, K)` is a quasi-isomorphism, the map along `a ≫ b` is a
quasi-isomorphism exactly when the base change along `𝒪(y) ⟶ 𝒪(z)` of the map along `b` is. -/
theorem isIso_derivedSectionsBaseChange_comp_iff
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    {z y w : 𝒳.val.val.obj} (a : z ⟶ y) (b : y ⟶ w)
    (ha : IsIso (derivedSectionsBaseChange B S hS 𝒳 a K)) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳 (a ≫ b) K) ↔
      IsIso ((dBaseChange.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 y)
        (ambientRingStructureSheaf_mul_comm B S hS 𝒳 z)).map
          (derivedSectionsBaseChange B S hS 𝒳 b K)) :=
  Adjunction.isIso_homEquiv_symm_iff_of_comp
    (dBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map b.op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 w)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 y))
    (dBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 y)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 z))
    (dBaseChangeAdj.{u, u + 1} ((ambientRingStructureSheaf B S hS 𝒳).obj.map (a ≫ b).op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 w)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 z))
    (Functor.mapDerivedCategoryCompIsoOfCompIso
      (ModuleCat.restrictScalarsComp'.{u + 1}
        ((ambientRingStructureSheaf B S hS 𝒳).obj.map b.op).hom
        ((ambientRingStructureSheaf B S hS 𝒳).obj.map a.op).hom
        ((ambientRingStructureSheaf B S hS 𝒳).obj.map (a ≫ b).op).hom
        (by rw [op_comp, Functor.map_comp, RingCat.hom_comp])).symm).symm
    _ _ _ (derivedSectionsRestrict_comp_app.{_, _, _, u + 1, u + 1}
      (ambientRingStructureSheaf B S hS 𝒳) a b K) ha

section Covering

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)

/-- **Stacks 0H15, second paragraph of the proof: the question is local.** Let `K` have cohomology
sheaves in `LQCoh^fbc(𝒪_𝒳)` (module universe `u + 1`), let `a : x ⟶ x'` be a morphism of
`𝒳_{affine}` and `T` a covering sieve of `x'` for one of the five topologies of `𝒳_{affine}` (the
étale one in the source). If the map `RΓ(y, K) ⊗^L_{𝒪(y)} 𝒪(z) ⟶ RΓ(z, K)` of Stacks 0H15 is a
quasi-isomorphism for every arrow `z ⟶ y` of `𝒳_{affine}` whose target `y ⟶ x'` lies in `T`, then
it is one along `a`.

Refine `T` to a finite flat covering `y_k ⟶ x'` and set `P_k = x ×_{x'} y_k`. The maps along the
flat arrows `y_k ⟶ x'` and `P_k ⟶ x` are quasi-isomorphisms by the flat case of Stacks 0H15, and
along `P_k ⟶ y_k` by hypothesis. By transitivity along `P_k ⟶ y_k ⟶ x'` and `P_k ⟶ x ⟶ x'`, the
base change of the map along `a` to `𝒪(P_k)` is a quasi-isomorphism for each `k`, and
`𝒪(x) ⟶ ∏ 𝒪(P_k)` is faithfully flat. -/
theorem isIso_derivedSectionsBaseChange_of_covering
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (τ : SiteKind) {x x' : AffineCategory B S hS 𝒳.val.val.p} (a : x ⟶ x') (T : Sieve x')
    (hT : T ∈ associatedAffineTopology B S hS 𝒳.val.val.p
      (BigAffineFppf.siteKindTopology B S hS τ) x')
    (hloc : ∀ ⦃y : AffineCategory B S hS 𝒳.val.val.p⦄ (g : y ⟶ x'), T g →
      ∀ ⦃z : AffineCategory B S hS 𝒳.val.val.p⦄ (b : z ⟶ y),
        IsIso (derivedSectionsBaseChange B S hS 𝒳
          ((AffineCategory.inclusion B S hS 𝒳.val.val.p).map b) K)) :
    IsIso (derivedSectionsBaseChange B S hS 𝒳
      ((AffineCategory.inclusion B S hS 𝒳.val.val.p).map a) K) := by
  have hp : 𝒳.val.val.p.IsFiberedInGroupoids := 𝒳.val.isFiberedInGroupoids
  let ι := AffineCategory.inclusion B S hS 𝒳.val.val.p
  let L := AffineCategory.toScheme B S hS 𝒳.val.val.p
  let O := ambientRingStructureSheaf B S hS 𝒳
  have := AffineCategory.hasPullbacks B S hS 𝒳.val.val.p hp
  have := AffineCategory.preservesPullbacks_toScheme B S hS 𝒳.val.val.p hp
  obtain ⟨E', hfin, hflat, -, hle⟩ :=
    AffineCategory.exists_finite_flat_covering B S hS 𝒳.val.val.p hp τ T hT
  obtain ⟨hsurj, hfl⟩ := (Scheme.presieve₀_mem_precoverage_iff _).mp hflat
  -- the fibre products `P_k = x ×_{x'} y_k`, carried to fibre products of schemes
  have hsq : ∀ k, IsPullback (L.map (pullback.fst a (E'.f k))) (L.map (pullback.snd a (E'.f k)))
      (L.map a) (L.map (E'.f k)) := fun k =>
    Functor.map_isPullback L (IsPullback.of_hasPullback a (E'.f k))
  have hflg : ∀ k, Flat (L.map (E'.f k)) := hfl
  have hflfst : ∀ k, Flat (L.map (pullback.fst a (E'.f k))) := fun k =>
    MorphismProperty.of_isPullback (P := @Flat) (hsq k).flip (hflg k)
  -- the flat case of Stacks 0H15
  have hP1 : ∀ {y z : AffineCategory B S hS 𝒳.val.val.p} (b : z ⟶ y), Flat (L.map b) →
      IsIso (derivedSectionsBaseChange B S hS 𝒳 (ι.map b) K) := fun {y z} b hb =>
    isIso_derivedSectionsBaseChange_of_flat B S hS 𝒳 E h K hK (ι.map b) z.property y.property hb
  -- the base change of the map along `a` to each `𝒪(P_k)` is invertible
  have hk : ∀ k, IsIso ((dBaseChange.{u, u + 1} (O.obj.map (ι.map (pullback.fst a (E'.f k))).op)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x.obj)
      (ambientRingStructureSheaf_mul_comm B S hS 𝒳 (pullback a (E'.f k)).obj)).map
        (derivedSectionsBaseChange B S hS 𝒳 (ι.map a) K)) := fun k => by
    have h₁ : IsIso (derivedSectionsBaseChange B S hS 𝒳
        (ι.map (pullback.snd a (E'.f k)) ≫ ι.map (E'.f k)) K) :=
      (isIso_derivedSectionsBaseChange_comp_iff B S hS 𝒳 K _ _
        (hloc _ (hle _ (E'.sieve₀_f k)) _)).2
        (have := hP1 _ (hflg k); Functor.map_isIso _ _)
    rw [← ι.map_comp, ← pullback.condition, ι.map_comp] at h₁
    exact (isIso_derivedSectionsBaseChange_comp_iff B S hS 𝒳 K _ _ (hP1 _ (hflfst k))).1 h₁
  -- the maps `P_k ⟶ x` form a finite flat covering of `x`
  let F : PreZeroHypercover.{u + 1} x := ⟨E'.I₀, fun k => pullback a (E'.f k),
    fun k => pullback.fst a (E'.f k)⟩
  have hF : (F.map L).presieve₀ ∈ Scheme.precoverage @Flat (L.obj x) := by
    refine (Scheme.presieve₀_mem_precoverage_iff _).mpr ⟨fun ξ => ?_, hflfst⟩
    obtain ⟨k, η, hη⟩ := hsurj (L.map a ξ)
    obtain ⟨ζ, hζ, -⟩ := Scheme.Pullback.exists_preimage_pullback ξ η hη.symm
    refine ⟨k, (hsq k).isoPullback.inv ζ, ?_⟩
    change ((hsq k).isoPullback.inv ≫ L.map (pullback.fst a (E'.f k))) ζ = ξ
    rwa [IsPullback.isoPullback_inv_fst]
  exact isIso_of_isIso_dBaseChange_map.{u, u + 1}
    (ambientRingStructureSheaf_mul_comm B S hS 𝒳 x.obj)
    (fun k => ambientRingStructureSheaf_mul_comm B S hS 𝒳 (pullback a (E'.f k)).obj)
    (fun k => O.obj.map (ι.map (pullback.fst a (E'.f k))).op)
    (fun k => flat_structureSheaf_map_of_flat B S hS 𝒳.val.val.p hp B.topology le_rfl
      (ι.map (pullback.fst a (E'.f k))) (hflfst k) (pullback a (E'.f k)).property x.property)
    (AffineCategory.faithfullyFlat_pi_map B S hS 𝒳.val.val.p _ rfl F hfin hF)
    (derivedSectionsBaseChange B S hS 𝒳 (ι.map a) K) hk

/-- **Stacks 0H15, second paragraph of the proof**, globally: if every object `x'` of
`𝒳_{affine}` has a covering sieve `T` (for one of the five topologies of `𝒳_{affine}`) such that
the map of Stacks 0H15 is a quasi-isomorphism along every arrow `z ⟶ y` with `y ⟶ x'` in `T`,
then `K` has the derived base change property of Stacks 0H15. -/
theorem hasAffineDerivedSectionsBaseChange_of_covering
    (K : DerivedCategory (SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
    (hK : DerivedCategoryB.derivedCategoryB (sheafFlatBaseChangeModulesSucc B E h S hS 𝒳) K)
    (τ : SiteKind)
    (hloc : ∀ x' : AffineCategory B S hS 𝒳.val.val.p, ∃ T : Sieve x',
      T ∈ associatedAffineTopology B S hS 𝒳.val.val.p (BigAffineFppf.siteKindTopology B S hS τ) x' ∧
      ∀ ⦃y : AffineCategory B S hS 𝒳.val.val.p⦄ (g : y ⟶ x'), T g →
        ∀ ⦃z : AffineCategory B S hS 𝒳.val.val.p⦄ (b : z ⟶ y),
          IsIso (derivedSectionsBaseChange B S hS 𝒳
            ((AffineCategory.inclusion B S hS 𝒳.val.val.p).map b) K)) :
    HasAffineDerivedSectionsBaseChange B S hS 𝒳 K := by
  intro x x' a hx hx'
  obtain ⟨T, hT, hT'⟩ := hloc ⟨x', hx'⟩
  exact isIso_derivedSectionsBaseChange_of_covering B S hS 𝒳 E h K hK τ
    (x := ⟨x, hx⟩) (x' := ⟨x', hx'⟩) (ObjectProperty.homMk a) T hT hT'

end Covering

end AlgebraicGeometry.Stack.FlatFppf
