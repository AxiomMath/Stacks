module

public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneExceptionalIdealChart
public import StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupEquivalenceRelationTransitivity
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupTwistDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushTransitionNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.OverFunctorExact
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 085T (3): `𝒪_{X'}(1)` is descended along the datum fixed by the map `𝒪(1) ⟶ 𝒪`

Let `b : X' ⟶ X` be the blowing up of an algebraic space along a closed subspace `Z`
(Stacks 085Q), presented by `P_R ⇉ P_U` with atlas `φ : P_U ⟶ X'`, with exceptional divisor `E`.
`AlgebraicGeometry.Space.blowUpTwistDescentDatum` is the quasi-coherent module `(𝒪_{P_U}(1)^a, α')`
on the groupoid of that presentation from which `𝒪_{X'}(1)` is descended.  This file shows that
`α'` is **characterised without reference to `E`**: it is the unique morphism
`t^*𝒪_{P_U}(1)^a ⟶ s^*𝒪_{P_U}(1)^a` which intertwines `t^*c` and `s^*c` with the canonical
descent datum of the structure sheaf of `X'`, where

`c = (𝒪_{P_U}(1) ⟶ 𝒪_{P_U})^a ≫ u⁻¹ : 𝒪_{P_U}(1)^a ⟶ φ^*𝒪_{X'}`

is built from the canonical map `𝒪(1) ⟶ 𝒪` of the scheme blowup `P_U` — on the standard chart at
`a`, `t ↦ (t / a⁽¹⁾) · b^♯(a)` — and the identification `u : φ^*𝒪_{X'} ≅ 𝒪_{P_U}^a`, built from
`𝒪` alone.  Three links make this formal:

* **G1** (uniqueness): `α'` is the only transition compatible with the map
  `𝒪_{P_U}(1)^a ≅ φ^*𝓘_E ⟶ φ^*𝒪_{X'}` through which it is defined; pullback along the étale
  projections preserves monomorphisms.
* **G2** (the atlas): that map is `(blowUpChartTwistOneIsoIdealSheaf ≫ κ)^a ≫ u⁻¹`, `κ` the
  inclusion of the ideal sheaf of `E ×_{X'} P_U` into `𝒪_{P_U}`: the isomorphism
  `φ^*𝓘_Z ≅ (𝓘_{Z ×_X A})^a` commutes with the inclusions into `𝒪`, at any étale chart.
* **G3** (the chart): `blowUpChartTwistOneIsoIdealSheaf ≫ κ` is the pullback along the comparison
  `Stacks.Blowup.reesSituationBlowUpIso` of Stacks 02OS (3) followed by the inclusion into `𝒪`,
  i.e. the canonical map `𝒪(1) ⟶ 𝒪`; the transport of ideal sheaves across a square commutes
  with the inclusions.

## Main definitions

* `AlgebraicGeometry.Space.blowUpTwistSpaceNegOneIsoAssociatedInvertibleSheaf`: **Stacks 085T
  (3)**, the canonical isomorphism `𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`.
* `AlgebraicGeometry.Space.blowUpChartTwistOneToUnit`: the canonical map `𝒪_{P_U}(1) ⟶ 𝒪_{P_U}`.
* `AlgebraicGeometry.Space.modulePullbackChartToSpaceUnitIso` and
  `AlgebraicGeometry.Space.modulePullbackPresentationAtlasUnitIso`: `φ^*𝒪_X ≅ 𝒪_A^a` for an étale
  scheme chart, and at the atlas of a presentation, built from `𝒪` alone.
* `AlgebraicGeometry.Space.isoIdealSheafToUnit`: an isomorphism with an ideal sheaf followed by
  the inclusion into `𝒪`; `AlgebraicGeometry.Space.presentationUnitMap`: `γ ↦ γ^a ≫ u⁻¹`.
* `AlgebraicGeometry.Space.SpaceBaseCompatible`, `AlgebraicGeometry.Space.TransitionCompatible`
  and `AlgebraicGeometry.Space.AtlasMapComputes`: the compatibility conditions, as structures.

## Main results

* `AlgebraicGeometry.Space.eq_blowUpTwistDescentDatum_alpha_iff`: **a morphism is `α'` if and
  only if it is compatible with `c` and the canonical descent datum of `𝒪_{X'}`**; `c` involves
  neither `E` nor `𝓘_E`.
* `AlgebraicGeometry.Space.blowUpTwistCompatible_alpha` and
  `AlgebraicGeometry.Space.eq_blowUpTwistDescentDatum_alpha`: G1.
* `AlgebraicGeometry.Space.modulePullbackChartToSpaceDefiningIdealIso_hom_comp`,
  `AlgebraicGeometry.Space.modulePullbackPresentationAtlasDefiningIdealIso_hom_comp`,
  `AlgebraicGeometry.Space.atlasMapComputes_definingIdealSheaf` and
  `AlgebraicGeometry.Space.blowUpAtlasMapComputes_idealSheaf`: G2, at a chart, at the atlas of a
  presentation, and at the atlas of the blowup.
* `AlgebraicGeometry.Space.isoIdealSheafToUnit_mapIso_trans_idealSheafIsoPullbackOfSquare_symm`
  and `AlgebraicGeometry.Space.blowUpChartTwistOneIsoIdealSheaf_hom_comp_ι`: G3.
* `AlgebraicGeometry.Space.blowUpAtlasMapComputes_toUnit`: G2 and G3 combined.
* `AlgebraicGeometry.Space.mono_modulePullback_map_of_isEtale`: pullback of modules along an
  étale morphism of algebraic spaces preserves monomorphisms.

## Implementation notes

Every statement about the blowup is an instance, with all arguments given, of a statement proved
for variables, and the compatibility equations are fields of structures.  Two spellings meet at
the blowup — the chart `P.U`, `P.toSpace` of the presentation against `projChart`, `chart` of the
glueing data, and the category of modules of a scheme against that of its ringed space — and
comparing them in a concrete term (an equation written out, a `kernel.ι` re-elaborated, a
definition unfolded by the kernel) exhausts the heartbeat budget.  So every comparison of
spellings is made in a lemma about variables, and the instances at the blowup are syntactic; in
`AlgebraicGeometry.Space.atlasMapComputes_definingIdealSheaf` the closed immersion and the
isomorphism `L` are arguments, with the equations identifying them, for that reason.

## References

* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Etale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Pullback of modules along an étale morphism of algebraic spaces preserves
monomorphisms.**  It is étale restriction
(`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, Stacks Equation 03LW), a
pushforward of sheaves of modules, which reindexes sections and so preserves injectivity on
sections. -/
theorem mono_modulePullback_map_of_isEtale {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsEtale B S hS f.hom) {M N : Modules.{u, u} B S hS Y.1 Y.2} (g : M ⟶ N) (hg : Mono g) :
    Mono ((modulePullback B S hS f).map g) := by
  have : (etaleModulePullback.{u, u} B S hS f hf).PreservesMonomorphisms :=
    SheafOfModules.pushforward_preservesMonomorphisms (F := smallEtalePostcomp B S hS f hf) _
  have : (modulePullback B S hS f).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso (modulePullbackIsoEtaleModulePullback B S hS f hf).symm
  exact @Functor.map_mono _ _ _ _ (modulePullback B S hS f) ‹_› _ _ g hg

end Etale

section Transport

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} {G : GroupoidInAlgebraicSpaces B S hS A}

/-- The transition morphism of a transported quasi-coherent module is the transition morphism of
the original module, conjugated by the isomorphism. -/
theorem transportedQuasicoherentModule_alpha (Y : QuasicoherentModule B S hS G)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ Y.F.obj) :
    (transportedQuasicoherentModule Y E e).alpha =
      (modulePullback B S hS G.target).map e.hom ≫ Y.alpha ≫
        (modulePullback B S hS G.source).map e.inv :=
  rfl

/-- The canonical transition of a pulled-back module, conjugated by an isomorphism `e`, is
compatible with the pullbacks of `e ≫ φ^*ψ` for every `ψ : ℳ ⟶ 𝒩`. -/
theorem spaceBaseDescent_conj_comp {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) {M N : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ N)
    {E : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    (e : E ≅ (modulePullback B S hS φ).obj M) :
    ((modulePullback B S hS G.target).map e.hom ≫ spaceBaseDescent B S hS G φ hφ M ≫
        (modulePullback B S hS G.source).map e.inv) ≫
        (modulePullback B S hS G.source).map (e.hom ≫ (modulePullback B S hS φ).map ψ) =
      (modulePullback B S hS G.target).map (e.hom ≫ (modulePullback B S hS φ).map ψ) ≫
        spaceBaseDescent B S hS G φ hφ N := by
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    Iso.inv_hom_id_map_assoc, spaceBaseDescent_naturality, Category.assoc]

/-- The transition of `ℰ` transported from the module on the groupoid attached to `ℳ`
(Stacks 03M3) along `e : ℰ ≅ φ^*ℳ` is `t^*e ≫ α_ℳ ≫ s^*e⁻¹`, with `α_ℳ` the canonical
transition. -/
theorem transportedSpaceBase_alpha {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ (modulePullback B S hS φ).obj M.obj) :
    (transportedQuasicoherentModule ((quasicoherentFromSpaceBase B S hS G φ hφ).obj M) E e).alpha =
      (modulePullback B S hS G.target).map e.hom ≫ spaceBaseDescent B S hS G φ hφ M.obj ≫
        (modulePullback B S hS G.source).map e.inv :=
  (transportedQuasicoherentModule_alpha _ _ _).trans
    (congrArg (fun a => (modulePullback B S hS G.target).map e.hom ≫ a ≫
      (modulePullback B S hS G.source).map e.inv) (spaceBaseObj_alpha B S hS G φ hφ M))

/-- **Compatibility of a transition morphism with a map to a pulled-back module.**  Let
`φ : U ⟶ X` with `t ≫ φ = s ≫ φ`, let `ψ : ℳ ⟶ 𝒩` be a morphism of quasi-coherent `𝒪_X`-modules
and `e : ℰ ≅ φ^*ℳ`, and write `c = e ≫ φ^*ψ : ℰ ⟶ φ^*𝒩`.  A morphism `β : t^*ℰ ⟶ s^*ℰ` is
compatible when `β ≫ s^*c = t^*c ≫ α_𝒩`, where `α_𝒩` is the canonical transition of `φ^*𝒩`
(`AlgebraicGeometry.Space.spaceBaseDescent`).

It is a structure rather than a definition so that the equation is stored verbatim in the type
of its constructor: a definition has the proofs nested in its body abstracted into auxiliary
lemmas, and comparing the unfolded body with the equation written out then exhausts the
heartbeat budget at the blowup. -/
structure SpaceBaseCompatible {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ (modulePullback B S hS φ).obj M.obj)
    (β : (modulePullback B S hS G.target).obj E.obj ⟶
      (modulePullback B S hS G.source).obj E.obj) : Prop where
  /-- `β ≫ s^*c = t^*c ≫ α_𝒩` for `c = e ≫ φ^*ψ`. -/
  comm : β ≫ (modulePullback B S hS G.source).map (e.hom ≫ (modulePullback B S hS φ).map ψ.hom) =
    (modulePullback B S hS G.target).map (e.hom ≫ (modulePullback B S hS φ).map ψ.hom) ≫
      spaceBaseDescent B S hS G φ hφ N.obj

/-- `AlgebraicGeometry.Space.SpaceBaseCompatible`, unfolded. -/
theorem spaceBaseCompatible_iff {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ (modulePullback B S hS φ).obj M.obj)
    (β : (modulePullback B S hS G.target).obj E.obj ⟶
      (modulePullback B S hS G.source).obj E.obj) :
    SpaceBaseCompatible φ hφ ψ E e β ↔
      β ≫ (modulePullback B S hS G.source).map (e.hom ≫ (modulePullback B S hS φ).map ψ.hom) =
        (modulePullback B S hS G.target).map (e.hom ≫ (modulePullback B S hS φ).map ψ.hom) ≫
          spaceBaseDescent B S hS G φ hφ N.obj :=
  ⟨fun h => h.comm, fun h => ⟨h⟩⟩

/-- **The transition of a module transported from a pulled-back module is compatible with the
pullback of every morphism out of the base module.**  Let `Y = (φ^*ℳ, α_ℳ)` be the
quasi-coherent module on the groupoid attached to a quasi-coherent `𝒪_X`-module `ℳ` (Stacks
03M3), and `e : ℰ ≅ φ^*ℳ`.  For `ψ : ℳ ⟶ 𝒩`, the transition of `ℰ` transported along `e`
intertwines `t^*(e ≫ φ^*ψ)` and `s^*(e ≫ φ^*ψ)` with the canonical transition of `φ^*𝒩`. -/
theorem spaceBaseCompatible_transported_alpha {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ (modulePullback B S hS φ).obj M.obj) :
    SpaceBaseCompatible φ hφ ψ E e
      (transportedQuasicoherentModule
        ((quasicoherentFromSpaceBase B S hS G φ hφ).obj M) E e).alpha :=
  ⟨(congrArg (fun a => a ≫
      (modulePullback B S hS G.source).map (e.hom ≫ (modulePullback B S hS φ).map ψ.hom))
    (transportedSpaceBase_alpha φ hφ M E e)).trans
    (spaceBaseDescent_conj_comp φ hφ ψ.hom e)⟩

/-- **The transition of a transported pulled-back module is the only morphism compatible with a
monomorphism out of the base module.**  In the situation of
`AlgebraicGeometry.Space.spaceBaseCompatible_transported_alpha`, if `φ` and the source projection
are étale and `ψ` is a monomorphism, any `β : t^*ℰ ⟶ s^*ℰ` compatible with `e ≫ φ^*ψ` is the
transported transition. -/
theorem eq_transported_alpha_of_spaceBaseCompatible {X : AlgebraicSpaces B S hS}
    (φ : G.objects ⟶ X) (hφ : G.target ≫ φ = G.source ≫ φ) (hφe : IsEtale B S hS φ.hom)
    (hs : IsEtale B S hS G.source.hom)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) (hψ : Mono ψ.hom)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ (modulePullback B S hS φ).obj M.obj)
    (β : (modulePullback B S hS G.target).obj E.obj ⟶ (modulePullback B S hS G.source).obj E.obj)
    (hβ : SpaceBaseCompatible φ hφ ψ E e β) :
    β = (transportedQuasicoherentModule
      ((quasicoherentFromSpaceBase B S hS G φ hφ).obj M) E e).alpha := by
  have : Mono (e.hom ≫ (modulePullback B S hS φ).map ψ.hom) :=
    @mono_comp _ _ _ _ _ _ (IsIso.mono_of_iso _) _
      (mono_modulePullback_map_of_isEtale φ hφe ψ.hom hψ)
  have := mono_modulePullback_map_of_isEtale G.source hs _ this
  exact (cancel_mono _).1
    (hβ.comm.trans (spaceBaseCompatible_transported_alpha φ hφ ψ E e).comm.symm)

end Transport

section Generic

/-- **Pasting four commuting squares.** -/
theorem comp_paste₄ {C : Type*} [Category C] {X₀ X₁ X₂ X₃ X₄ Y₀ Y₁ Y₂ Y₃ Y₄ : C}
    (f₀ : X₀ ⟶ Y₀) (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (f₃ : X₃ ⟶ Y₃) (f₄ : X₄ ⟶ Y₄)
    (a₁ : X₀ ⟶ X₁) (a₂ : X₁ ⟶ X₂) (a₃ : X₂ ⟶ X₃) (a₄ : X₃ ⟶ X₄)
    (b₁ : Y₀ ⟶ Y₁) (b₂ : Y₁ ⟶ Y₂) (b₃ : Y₂ ⟶ Y₃) (b₄ : Y₃ ⟶ Y₄)
    (h₁ : f₀ ≫ b₁ = a₁ ≫ f₁) (h₂ : f₁ ≫ b₂ = a₂ ≫ f₂) (h₃ : f₂ ≫ b₃ = a₃ ≫ f₃)
    (h₄ : f₃ ≫ b₄ = a₄ ≫ f₄) :
    f₀ ≫ b₁ ≫ b₂ ≫ b₃ ≫ b₄ = (a₁ ≫ a₂ ≫ a₃ ≫ a₄) ≫ f₄ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]
  simp only [Category.assoc]

/-- The counit of the equivalence of full subcategories induced by an equivalence is natural,
read through the inclusions. -/
theorem ι_map_congrFullSubcategory_counit_naturality {C D : Type*} [Category C] [Category D]
    {P : ObjectProperty C} {Q : ObjectProperty D} (e : C ≌ D) [Q.IsClosedUnderIsomorphisms]
    (h : Q.inverseImage e.functor = P) {Y Y' : Q.FullSubcategory} (f : Y ⟶ Y') :
    e.functor.map (e.inverse.map f.hom) ≫
        Q.ι.map ((e.congrFullSubcategory h).counitIso.hom.app Y') =
      Q.ι.map ((e.congrFullSubcategory h).counitIso.hom.app Y) ≫ f.hom :=
  e.counit.naturality f.hom

/-- **The comparison of an inclusion through two chains of isomorphisms.**  Given
`r_I : R c_I ≅ p_I`, `r_O : R c_O ≅ p_O`, `s_I : c_I ≅ q_I`, `s_O : c_O ≅ q_O`, `k : q_I ≅ k_I`,
`w : U ≅ q_O` and maps `m`, `n`, `p`, `ι` making the three squares commute, the composite
`r_I⁻¹ ≫ R(s_I ≫ k)` intertwines `R ι` and `p` with `r_O⁻¹ ≫ R(s_O ≫ w⁻¹)`. -/
theorem iso_chain_comp_map {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {cI cO qI qO kI U : C} {pI pO : D} (rI : R.obj cI ≅ pI) (rO : R.obj cO ≅ pO)
    (sI : cI ≅ qI) (sO : cO ≅ qO) (k : qI ≅ kI) (w : U ≅ qO) (m : cI ⟶ cO) (n : qI ⟶ qO)
    (p : pI ⟶ pO) (ι : kI ⟶ U) (hr : R.map m ≫ rO.hom = rI.hom ≫ p)
    (hs : m ≫ sO.hom = sI.hom ≫ n) (hk : k.hom ≫ ι = n ≫ w.inv) :
    (rI.symm ≪≫ R.mapIso (sI ≪≫ k)).hom ≫ R.map ι =
      p ≫ (rO.symm ≪≫ R.mapIso (sO ≪≫ w.symm)).hom := by
  have hr' : rI.inv ≫ R.map m = p ≫ rO.inv := (CommSq.mk hr.symm).horiz_inv.w
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← R.map_comp, Category.assoc, hk, ← reassoc_of% hs, R.map_comp, reassoc_of% hr']

/-- **An isomorphism read through a functor and then an identification, against two maps.**
For `h : a ≅ b`, `L : x ≅ F b`, `u : y ≅ F o` and maps `ι : x ⟶ y`, `κ : b ⟶ o` with
`L ≫ F κ = ι ≫ u`, the composite `F h ≫ L⁻¹ ≫ ι` is `F (h ≫ κ) ≫ u⁻¹`. -/
theorem mapIso_trans_symm_hom_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b o : C} {x y : D} (h : a ≅ b) (L : x ≅ F.obj b) (ι : x ⟶ y) (κ : b ⟶ o)
    (u : y ≅ F.obj o) (hL : L.hom ≫ F.map κ = ι ≫ u.hom) :
    (F.mapIso h ≪≫ L.symm).hom ≫ ι = F.map (h.hom ≫ κ) ≫ u.inv := by
  have h' : L.inv ≫ ι = F.map κ ≫ u.inv := (CommSq.mk hL).horiz_inv.w
  rw [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc, h', F.map_comp,
    Category.assoc]

end Generic

section SchemeTransport

/-- **The map to `𝒪` attached to an isomorphism with an ideal sheaf**: for `g : W ⟶ T` and
`h : ℰ ≅ 𝓘(g)`, the isomorphism `h` followed by the inclusion `𝓘(g) ⟶ 𝒪_T`. -/
def isoIdealSheafToUnit {W T : Scheme.{u}} (g : W ⟶ T) {E : T.Modules}
    (h : E ≅ Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom) :
    E ⟶ SheafOfModules.unit (structureSheafRing T.toSheafedSpace) :=
  h.hom ≫ kernel.ι (C := T.Modules) (SheafOfModules.unitToPushforwardObjUnit
    (RingedSpaceModuleAdjunction.structureSheafHom g.toLRSHom.toShHom))

/-- **The transport of an ideal sheaf across a square commutes with the inclusions into `𝒪`.**
For a square `f ≫ β = ε ≫ k` with `ε` and `β` isomorphisms of schemes and any isomorphism
`c : M ≅ 𝓘(k)`, the isomorphism `β^*M ≅ 𝓘(f)` obtained from `β^*c` and
`Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare`, followed by the
inclusion `𝓘(f) ⟶ 𝒪_T`, is `β^*` of `c` followed by the inclusion `𝓘(k) ⟶ 𝒪_{T'}`, read
through the identification `β^*𝒪_{T'} ≅ 𝒪_T`. -/
theorem isoIdealSheafToUnit_mapIso_trans_idealSheafIsoPullbackOfSquare_symm
    {S S' T T' : Scheme.{u}} (f : S ⟶ T) (ε : S ≅ S') (k : S' ⟶ T') (β : T ≅ T')
    (hsq : f ≫ β.hom = ε.hom ≫ k) {M : T'.Modules}
    (c : M ≅ Stacks.ClosedImmersion.idealSheaf k.toLRSHom.toShHom) :
    isoIdealSheafToUnit f
        ((RingedSpaceModuleAdjunction.modulePullback β.hom.toLRSHom.toShHom).mapIso c ≪≫
          (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare f
            ε k β hsq).symm) =
      (RingedSpaceModuleAdjunction.modulePullback β.hom.toLRSHom.toShHom).map (c.hom ≫
          kernel.ι (SheafOfModules.unitToPushforwardObjUnit
            (RingedSpaceModuleAdjunction.structureSheafHom k.toLRSHom.toShHom))) ≫
        (Stacks.IdealSheafRestrict.pullbackUnitIso β.hom).hom :=
  (Category.assoc _ _ _).trans ((congrArg (fun g =>
      (RingedSpaceModuleAdjunction.modulePullback β.hom.toLRSHom.toShHom).map c.hom ≫ g)
    (Stacks.Conormal.AffineCotangent.SourceTransport.idealSheafIsoPullbackOfSquare_inv_comp_ι
      f ε k β hsq)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫
      (Stacks.IdealSheafRestrict.pullbackUnitIso β.hom).hom)
      ((RingedSpaceModuleAdjunction.modulePullback β.hom.toLRSHom.toShHom).map_comp _ _).symm)))

end SchemeTransport


section Chart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (A : SmallEtale B S hS X.1)

/-- The first factor of `AlgebraicGeometry.Space.representedAssociatedChartSchemeModuleIso` is
natural in the module. -/
theorem representedAssociatedModuleChartSchemeModuleIso_naturality
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (ψ : M ⟶ N) :
    (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).map
        ((chartSchemeModuleFunctor B S hS X A).map ψ) ≫
      (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X A)).functor.map
        (associatedModuleChartSchemeModuleIso B S hS X N.obj N.property A).hom =
    (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X A)).functor.map
        (associatedModuleChartSchemeModuleIso B S hS X M.obj M.property A).hom ≫
      (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X A)).functor.map
        ((chartSchemeEtaleModuleFunctor B S hS X A).map ψ) :=
  ((representedSmallEtaleModuleEquivalence B S hS
      (chartFppfObject B S hS X A)).functor.map_comp _ _).symm.trans
    ((congrArg (representedSmallEtaleModuleEquivalence B S hS
        (chartFppfObject B S hS X A)).functor.map
      (associatedModuleChartSchemeModuleIso_naturality B S hS X A ψ)).trans
      ((representedSmallEtaleModuleEquivalence B S hS
        (chartFppfObject B S hS X A)).functor.map_comp _ _))

/-- The counit `AlgebraicGeometry.Space.representedSmallEtaleChartSchemeEtaleModuleIso` of the
comparison of Stacks 03DX (2) at an étale chart is natural in the module. -/
theorem representedSmallEtaleChartSchemeEtaleModuleIso_naturality
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (ψ : M ⟶ N) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS ((SmallEtale.toOver B S hS X.1).obj A))).ι.map
        ((representedQuasicoherentEquivalence B S hS
            ((SmallEtale.toOver B S hS X.1).obj A)).functor.map
          ((representedQuasicoherentEquivalence B S hS
              ((SmallEtale.toOver B S hS X.1).obj A)).inverse.map
            ((chartSmallEtaleQcohFunctor B S hS X A).map ψ))) ≫
      (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X N.obj N.property A).hom =
    (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X M.obj M.property A).hom ≫
      (chartSchemeRestrictionFunctor B S hS X A).map ψ.hom :=
  have h := congrArg (fun k => (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS ((SmallEtale.toOver B S hS X.1).obj A))).ι.map k)
    ((representedQuasicoherentEquivalence B S hS
        ((SmallEtale.toOver B S hS X.1).obj A)).counitIso.hom.naturality
      ((chartSmallEtaleQcohFunctor B S hS X A).map ψ))
  ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS ((SmallEtale.toOver B S hS X.1).obj A))).ι.map_comp
        _ _).symm.trans
    (h.trans ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS ((SmallEtale.toOver B S hS X.1).obj A))).ι.map_comp
        _ _))

/-- The two readings of the chart restriction of a morphism on the small étale site of the chart
space agree. -/
theorem representedSmallEtaleModuleEquivalence_map_chartSchemeEtaleModuleFunctor_map
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (ψ : M ⟶ N) :
    (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS X A)).functor.map
        ((chartSchemeEtaleModuleFunctor B S hS X A).map ψ) =
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (representedStructureRingSheaf B S hS ((SmallEtale.toOver B S hS X.1).obj A))).ι.map
        ((representedQuasicoherentEquivalence B S hS
            ((SmallEtale.toOver B S hS X.1).obj A)).functor.map
          ((representedQuasicoherentEquivalence B S hS
              ((SmallEtale.toOver B S hS X.1).obj A)).inverse.map
            ((chartSmallEtaleQcohFunctor B S hS X A).map ψ))) :=
  rfl

/-- The identification `AlgebraicGeometry.Space.chartSmallEtaleRestrictionFunctorObjIso` of the
restriction to an étale chart with étale restriction is natural in the module: both sides are
the module itself on sections. -/
theorem chartSmallEtaleRestrictionFunctorObjIso_naturality
    {M N : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ N) :
    (chartSchemeRestrictionFunctor B S hS X A).map ψ ≫
        (chartSmallEtaleRestrictionFunctorObjIso X N A).hom =
      (chartSmallEtaleRestrictionFunctorObjIso X M A).hom ≫
        (etaleModulePullback B S hS (chartToSpace B S hS X A)
          (isEtale_chartToSpace B S hS X A)).map ψ :=
  Stacks.SheafOfModules.comp_eq_of_forall_val_app_apply _ _ _ _ fun _ _ => rfl

/-- **`AlgebraicGeometry.Space.representedAssociatedChartSchemeModuleIso` is natural in the
module.** -/
theorem representedAssociatedChartSchemeModuleIso_naturality
    {M N : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureRingSheaf B S hS X)).FullSubcategory} (ψ : M ⟶ N) :
    (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).map
        ((chartSchemeModuleFunctor B S hS X A).map ψ) ≫
      (representedAssociatedChartSchemeModuleIso B S hS X A N.obj N.property).hom =
    (representedAssociatedChartSchemeModuleIso B S hS X A M.obj M.property).hom ≫
      (modulePullback B S hS (chartToSpace B S hS X A)).map ψ.hom :=
  comp_paste₄ _ _ _ _ _ _ _ _ _ _ _ _ _
    (representedAssociatedModuleChartSchemeModuleIso_naturality B S hS X A ψ)
    ((congrArg (fun k => k ≫ (representedSmallEtaleChartSchemeEtaleModuleIso B S hS X N.obj
        N.property A).hom)
      (representedSmallEtaleModuleEquivalence_map_chartSchemeEtaleModuleFunctor_map
        B S hS X A ψ)).trans
      (representedSmallEtaleChartSchemeEtaleModuleIso_naturality B S hS X A ψ))
    (chartSmallEtaleRestrictionFunctorObjIso_naturality B S hS X A ψ.hom)
    ((modulePullbackIsoEtaleModulePullback B S hS (chartToSpace B S hS X A)
      (isEtale_chartToSpace B S hS X A)).inv.naturality ψ.hom)

/-- **The comparison of Stacks 085T's module-level step, for the structure sheaf**: the pullback
of `𝒪_X` along an étale scheme chart `A ⟶ X` is the module associated with `𝒪_A`.  It is
`AlgebraicGeometry.Space.representedAssociatedChartSchemeModuleIso` read through
`AlgebraicGeometry.Space.chartSchemeModuleIsoChartPush` and
`AlgebraicGeometry.Space.chartPushUnitIso`, and involves no closed subspace. -/
def modulePullbackChartToSpaceUnitIso :
    (modulePullback B S hS (chartToSpace B S hS X A)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ≅
      (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).obj
        (SheafOfModules.unit (chartScheme A).ringCatSheaf) :=
  (representedAssociatedChartSchemeModuleIso B S hS X A _
      (SheafOfModules.isQuasicoherentOnSite_unit _)).symm ≪≫
    (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).mapIso
      (chartSchemeModuleIsoChartPush B S hS X _ (SheafOfModules.isQuasicoherentOnSite_unit _) A ≪≫
        (chartPushUnitIso B S hS X A).symm)

variable (Z : ClosedSubspaces B S hS X.1)

/-- The identification `AlgebraicGeometry.Space.chartPushDefiningIdealIso` of the chart
restriction of `𝓘_Z` with the ideal sheaf of `Z ×_X A ⟶ A` commutes with the inclusions into
`𝒪_A`. -/
theorem chartPushDefiningIdealIso_hom_comp_kernelι :
    (chartPushDefiningIdealIso B S hS X A Z).hom ≫
        kernel.ι (C := (chartScheme A).Modules) (SheafOfModules.unitToPushforwardObjUnit
          (RingedSpaceModuleAdjunction.structureSheafHom ((BigFppfOver.toScheme B S hS).map
            (Z.2.2.rep.snd A.1.hom)).toLRSHom.toShHom)) =
      chartPushDefiningIdealι B S hS X A Z :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun g => chartPushDefiningIdealFactor B S hS X A Z ≫ g)
      (kernel.lift_ι (C := (chartScheme A).Modules) _ _ _)).trans
      (SheafOfModules.Submodule.factorThru_ι _ _ _))

/-- **The isomorphism `φ^*𝓘_Z ≅ (𝓘_{Z ×_X A})^a` commutes with the inclusions into `𝒪`.**  For an
étale scheme chart `φ : A ⟶ X` and a closed subspace `Z ⊆ X`, the isomorphism
`AlgebraicGeometry.Space.modulePullbackChartToSpaceDefiningIdealIso` followed by the inclusion
of the ideal sheaf of `Z ×_X A ⟶ A` into `𝒪_A` is the pullback of the inclusion `𝓘_Z ⟶ 𝒪_X`
followed by the identification `AlgebraicGeometry.Space.modulePullbackChartToSpaceUnitIso`, which
does not involve `Z`. -/
theorem modulePullbackChartToSpaceDefiningIdealIso_hom_comp :
    (modulePullbackChartToSpaceDefiningIdealIso B S hS X A Z).hom ≫
        (representedAssociatedModuleFunctor B S hS (chartFppfObject B S hS X A)).map
          (kernel.ι (C := (chartScheme A).Modules) (SheafOfModules.unitToPushforwardObjUnit
            (RingedSpaceModuleAdjunction.structureSheafHom ((BigFppfOver.toScheme B S hS).map
              (Z.2.2.rep.snd A.1.hom)).toLRSHom.toShHom))) =
      (modulePullback B S hS (chartToSpace B S hS X A)).map (definingIdealSheaf B S hS X Z).ι ≫
        (modulePullbackChartToSpaceUnitIso B S hS X A).hom :=
  iso_chain_comp_map _ _ _ _ _ _ _ _ _ _ _
    (representedAssociatedChartSchemeModuleIso_naturality B S hS X A
      (M := ⟨_, isQuasicoherentOnSite_definingIdealSheaf B S hS X Z⟩)
      (N := ⟨_, SheafOfModules.isQuasicoherentOnSite_unit _⟩)
      (ObjectProperty.homMk (definingIdealSheaf B S hS X Z).ι))
    (chartSchemeModuleIsoChartPush_naturality B S hS X A
      (M' := ⟨_, isQuasicoherentOnSite_definingIdealSheaf B S hS X Z⟩)
      (L' := ⟨_, SheafOfModules.isQuasicoherentOnSite_unit _⟩)
      (ObjectProperty.homMk (definingIdealSheaf B S hS X Z).ι))
    (chartPushDefiningIdealIso_hom_comp_kernelι B S hS X A Z)

end Chart

section Presentation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Compatibility of a transition morphism with a map to a pulled-back module.**  Let
`φ : U ⟶ X` with `t ≫ φ = s ≫ φ`, `𝒩` an `𝒪_X`-module and `c : ℰ ⟶ φ^*𝒩`.  A morphism
`β : t^*ℰ ⟶ s^*ℰ` is compatible with `c` when `β ≫ s^*c = t^*c ≫ α_𝒩`, where `α_𝒩` is the
canonical transition of `φ^*𝒩` (`AlgebraicGeometry.Space.spaceBaseDescent`).  Unlike
`AlgebraicGeometry.Space.SpaceBaseCompatible`, `c` is arbitrary rather than of the form
`e ≫ φ^*ψ`.  It is a structure for the reason given there. -/
structure TransitionCompatible {A : AlgebraicSpaces B S hS}
    {G : GroupoidInAlgebraicSpaces B S hS A} {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (N : Modules.{u, u} B S hS X.1 X.2)
    {E : Modules.{u, u} B S hS G.objects.1 G.objects.2}
    (c : E ⟶ (modulePullback B S hS φ).obj N)
    (β : (modulePullback B S hS G.target).obj E ⟶ (modulePullback B S hS G.source).obj E) :
    Prop where
  /-- `β ≫ s^*c = t^*c ≫ α_𝒩`. -/
  comm : β ≫ (modulePullback B S hS G.source).map c =
    (modulePullback B S hS G.target).map c ≫ spaceBaseDescent B S hS G φ hφ N

/-- **Compatibility with `e ≫ φ^*ψ` is compatibility with any map equal to it.** -/
theorem spaceBaseCompatible_iff_transitionCompatible {A : AlgebraicSpaces B S hS}
    {G : GroupoidInAlgebraicSpaces B S hS A} {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N)
    (E : QuasicoherentSheaves.{u, u} B S hS G.objects.obj G.objects.property)
    (e : E.obj ≅ (modulePullback B S hS φ).obj M.obj)
    {c : E.obj ⟶ (modulePullback B S hS φ).obj N.obj}
    (hc : e.hom ≫ (modulePullback B S hS φ).map ψ.hom = c)
    (β : (modulePullback B S hS G.target).obj E.obj ⟶
      (modulePullback B S hS G.source).obj E.obj) :
    SpaceBaseCompatible φ hφ ψ E e β ↔ TransitionCompatible φ hφ N.obj c β := by
  subst hc
  exact ⟨fun h => ⟨h.comm⟩, fun h => ⟨h.comm⟩⟩

variable {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- `AlgebraicGeometry.Space.modulePullbackChartToSpaceUnitIso` at the atlas of a presentation:
the pullback of `𝒪_X` along the atlas `U ⟶ X` is the module associated with `𝒪_U`. -/
def modulePullbackPresentationAtlasUnitIso (P : Presentation B S hS X.1 X.2) :
    (modulePullback B S hS (presentationAtlas P)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ≅
      (presentationObjectsFunctor P).obj
        (SheafOfModules.unit ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf) :=
  modulePullbackChartToSpaceUnitIso B S hS X (presentationChart P)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- Pullback along the atlas of a presentation is pullback along the chart
`AlgebraicGeometry.Space.presentationChart`. -/
theorem modulePullback_presentationAtlas_eq (P : Presentation B S hS X.1 X.2) :
    modulePullback B S hS (presentationAtlas P) =
      modulePullback B S hS (chartToSpace B S hS X (presentationChart P)) :=
  rfl

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- The pullback of a morphism along the atlas of a presentation is its pullback along the chart
`AlgebraicGeometry.Space.presentationChart`. -/
theorem modulePullback_presentationAtlas_map (P : Presentation B S hS X.1 X.2)
    {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) :
    (modulePullback B S hS (presentationAtlas P)).map f =
      (modulePullback B S hS (chartToSpace B S hS X (presentationChart P))).map f :=
  eq_of_heq (Functor.hcongr_hom (modulePullback_presentationAtlas_eq P) f)

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **`AlgebraicGeometry.Space.modulePullbackChartToSpaceDefiningIdealIso_hom_comp` at the atlas
of a presentation**: the isomorphism `φ^*𝓘_Z ≅ (𝓘_{Z ×_X U})^a` of
`AlgebraicGeometry.Space.modulePullbackPresentationAtlasDefiningIdealIso` commutes with the
inclusions into `𝒪`. -/
theorem modulePullbackPresentationAtlasDefiningIdealIso_hom_comp (Z : ClosedSubspaces B S hS X.1)
    (P : Presentation B S hS X.1 X.2) :
    (modulePullbackPresentationAtlasDefiningIdealIso B S hS X Z P).hom ≫
        (presentationObjectsFunctor P).map
          (kernel.ι (C := ((BigFppfOver.toScheme B S hS).obj P.U).Modules)
            (SheafOfModules.unitToPushforwardObjUnit
              (RingedSpaceModuleAdjunction.structureSheafHom ((BigFppfOver.toScheme B S hS).map
                (Z.2.2.rep.snd P.toSpace)).toLRSHom.toShHom))) =
      (modulePullback B S hS (presentationAtlas P)).map (definingIdealSheaf B S hS X Z).ι ≫
        (modulePullbackPresentationAtlasUnitIso P).hom :=
  (modulePullbackChartToSpaceDefiningIdealIso_hom_comp B S hS X (presentationChart P) Z).trans
    (congrArg (fun g => g ≫ (modulePullbackPresentationAtlasUnitIso P).hom)
      (modulePullback_presentationAtlas_map P (definingIdealSheaf B S hS X Z).ι).symm)

/-- **The map `ℰ^a ⟶ φ^*𝒪_X` attached to a map `γ : ℰ ⟶ 𝒪_U` on the presenting scheme** of a
presentation `X = U/R` with atlas `φ`: `γ^a` followed by the inverse of
`AlgebraicGeometry.Space.modulePullbackPresentationAtlasUnitIso`. -/
def presentationUnitMap (P : Presentation B S hS X.1 X.2)
    {E : ((BigFppfOver.toScheme B S hS).obj P.U).Modules}
    (γ : E ⟶ SheafOfModules.unit
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj P.U).toSheafedSpace)) :
    (presentationObjectsFunctor P).obj E ⟶ (modulePullback B S hS (presentationAtlas P)).obj
      (SheafOfModules.unit (structureRingSheaf B S hS X)) :=
  (presentationObjectsFunctor P).map γ ≫ (modulePullbackPresentationAtlasUnitIso P).inv

/-- **A map to the pulled-back structure sheaf, computed on the presenting scheme.**  For a
presentation `X = U/R` with atlas `φ : U ⟶ X`, a morphism `ψ : ℳ ⟶ 𝒪_X`, a Zariski module `ℰ`
on `U` and `e : ℰ^a ≅ φ^*ℳ`, a morphism `γ : ℰ ⟶ 𝒪_U` *computes* `e ≫ φ^*ψ` when
`e ≫ φ^*ψ = γ^a ≫ u⁻¹` (`AlgebraicGeometry.Space.presentationUnitMap`), where
`u : φ^*𝒪_X ≅ 𝒪_U^a` is `AlgebraicGeometry.Space.modulePullbackPresentationAtlasUnitIso`, built
from `𝒪` alone.

It is a structure, for the reason given at `AlgebraicGeometry.Space.SpaceBaseCompatible`. -/
structure AtlasMapComputes (P : Presentation B S hS X.1 X.2)
    {M : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X))
    {E : ((BigFppfOver.toScheme B S hS).obj P.U).Modules}
    (e : (presentationObjectsFunctor P).obj E ≅ (modulePullback B S hS (presentationAtlas P)).obj M)
    (γ : E ⟶ SheafOfModules.unit
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj P.U).toSheafedSpace)) : Prop where
  /-- `e ≫ φ^*ψ = γ^a ≫ u⁻¹`. -/
  comm : e.hom ≫ (modulePullback B S hS (presentationAtlas P)).map ψ = presentationUnitMap P γ

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- `AlgebraicGeometry.Space.AtlasMapComputes` is invariant under replacing `γ` by an equal
morphism. -/
theorem AtlasMapComputes.of_eq {P : Presentation B S hS X.1 X.2}
    {M : Modules.{u, u} B S hS X.1 X.2} {ψ : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)}
    {E : ((BigFppfOver.toScheme B S hS).obj P.U).Modules}
    {e : (presentationObjectsFunctor P).obj E ≅ (modulePullback B S hS (presentationAtlas P)).obj M}
    {γ γ' : E ⟶ SheafOfModules.unit
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj P.U).toSheafedSpace)}
    (h : AtlasMapComputes P ψ e γ) (hγ : γ = γ') : AtlasMapComputes P ψ e γ' :=
  hγ ▸ h

omit [HasSheafify (BigFppfOver.topology B S hS) (Type u)] in
/-- **Stacks 085T's module-level step at the atlas of a presentation, against the inclusions.**
For a closed subspace `Z ⊆ X` and a presentation `X = U/R` with atlas `φ`, let `g` be the closed
immersion `Z ×_X U ⟶ U` and `L : φ^*𝓘_Z ≅ 𝓘(g)^a` the isomorphism
`AlgebraicGeometry.Space.modulePullbackPresentationAtlasDefiningIdealIso` (both are taken as
arguments together with the equations identifying them, so that they can be supplied in any
spelling).  For any isomorphism `h : ℰ ≅ 𝓘(g)`, the map `ℰ^a ⟶ φ^*𝒪_X` obtained from `h` and `L`,
followed by `φ^*` of the inclusion `𝓘_Z ⟶ 𝒪_X`, is computed on `U` by `h` followed by the
inclusion of `𝓘(g)` into `𝒪_U`.  This is
`AlgebraicGeometry.Space.modulePullbackChartToSpaceDefiningIdealIso_hom_comp` at the chart
`AlgebraicGeometry.Space.presentationChart`. -/
theorem atlasMapComputes_definingIdealSheaf (Z : ClosedSubspaces B S hS X.1)
    (P : Presentation B S hS X.1 X.2)
    (g : (BigFppfOver.toScheme B S hS).obj (Z.2.2.rep.pullback P.toSpace) ⟶
      (BigFppfOver.toScheme B S hS).obj P.U)
    (hg : g = (BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd P.toSpace))
    {E : ((BigFppfOver.toScheme B S hS).obj P.U).Modules}
    (h : E ≅ Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom)
    (L : (modulePullback B S hS (presentationAtlas P)).obj
        (definingIdealSheaf B S hS X Z).toSheafOfModules ≅
      (presentationObjectsFunctor P).obj
        (Stacks.ClosedImmersion.idealSheaf g.toLRSHom.toShHom))
    (hL : HEq L (modulePullbackPresentationAtlasDefiningIdealIso B S hS X Z P)) :
    AtlasMapComputes P (definingIdealSheaf B S hS X Z).ι
      ((presentationObjectsFunctor P).mapIso h ≪≫ L.symm) (isoIdealSheafToUnit g h) := by
  subst hg
  obtain rfl := eq_of_heq hL
  exact ⟨mapIso_trans_symm_hom_comp (presentationObjectsFunctor P) h
    (modulePullbackPresentationAtlasDefiningIdealIso B S hS X Z P) _ _
    (modulePullbackPresentationAtlasUnitIso P)
    (modulePullbackPresentationAtlasDefiningIdealIso_hom_comp Z P)⟩


end Presentation

section Blowup

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
  (Z : ClosedSubspaces B S hS X.obj) (P : Presentation B S hS X.obj X.property)
  (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
  (heq : CategoryTheory.IsEquivalenceRelation
      ((Over.post B.inclusion).map (reesProjTarget (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR))
      ((Over.post B.inclusion).map (reesProjSource (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR)))

/-- The structure sheaf `𝒪_{X'}` of the blowup, as a quasi-coherent `𝒪_{X'}`-module. -/
abbrev blowUpStructureQcoh :
    QuasicoherentSheaves.{u, u} B S hS (blowUpAlong Z P hcU hcR heq).obj
      (blowUpAlong Z P hcU hcR heq).property :=
  ⟨SheafOfModules.unit (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)),
    SheafOfModules.isQuasicoherentOnSite_unit _⟩

/-- The inclusion `𝓘_E ⟶ 𝒪_{X'}`, as a morphism of quasi-coherent `𝒪_{X'}`-modules. -/
abbrev exceptionalIdealQcohι :
    exceptionalIdealQcoh Z P hcU hcR heq ⟶ blowUpStructureQcoh Z P hcU hcR heq :=
  ObjectProperty.homMk (definingIdealSheaf B S hS (blowUpAlong Z P hcU hcR heq)
    (exceptionalDivisor Z P hcU hcR heq)).ι

/-- The inclusion `𝓘_E ⟶ 𝒪_{X'}` is a monomorphism. -/
theorem mono_exceptionalIdealQcohι_hom : Mono (exceptionalIdealQcohι Z P hcU hcR heq).hom :=
  SheafOfModules.Submodule.mono_ι_via_forget (definingIdealSheaf B S hS
    (blowUpAlong Z P hcU hcR heq) (exceptionalDivisor Z P hcU hcR heq))

/-- **The transition `α'` of `(𝒪_{P_U}(1)^a, α')` is compatible with
`c : 𝒪_{P_U}(1)^a ⟶ φ^*𝒪_{X'}`**: `α' ≫ s^*c = t^*c ≫ α_𝒪`, where `α_𝒪` is the canonical
descent datum of the structure sheaf of `X'` on `P_R ⇉ P_U`. -/
theorem blowUpTwistCompatible_alpha :
    SpaceBaseCompatible _ (presentationAtlas_comm (blowUpPresentation Z P hcU hcR heq))
      (exceptionalIdealQcohι Z P hcU hcR heq) (blowUpChartTwistOneQcoh Z P hcU hcR heq)
      (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq)
      (blowUpTwistDescentDatum Z P hcU hcR heq).alpha :=
  spaceBaseCompatible_transported_alpha _ _ _ _ _

/-- **`α'` is the only transition morphism compatible with `c`.**  Any morphism
`β : t^*𝒪_{P_U}(1)^a ⟶ s^*𝒪_{P_U}(1)^a` with `β ≫ s^*c = t^*c ≫ α_𝒪` is the transition `α'`
of `AlgebraicGeometry.Space.blowUpTwistDescentDatum`: `c` is a monomorphism and pullback along
the étale source projection preserves monomorphisms. -/
theorem eq_blowUpTwistDescentDatum_alpha
    (β : (modulePullback B S hS
          (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)).target).obj
          (blowUpChartTwistOneQcoh Z P hcU hcR heq).obj ⟶
        (modulePullback B S hS
          (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)).source).obj
          (blowUpChartTwistOneQcoh Z P hcU hcR heq).obj)
    (hβ : SpaceBaseCompatible _ (presentationAtlas_comm (blowUpPresentation Z P hcU hcR heq))
      (exceptionalIdealQcohι Z P hcU hcR heq) (blowUpChartTwistOneQcoh Z P hcU hcR heq)
      (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq) β) :
    β = (blowUpTwistDescentDatum Z P hcU hcR heq).alpha :=
  eq_transported_alpha_of_spaceBaseCompatible _ _
    (presentationAtlas_isEtale (blowUpPresentation Z P hcU hcR heq))
    (presentationGroupoid_source_isEtale (blowUpPresentation Z P hcU hcR heq)) _
    (mono_exceptionalIdealQcohι_hom Z P hcU hcR heq) _ _ β hβ

/-- **The canonical map `𝒪_{P_U}(1) ⟶ 𝒪_{P_U}`** on the étale chart of the blowup.  On the
blowup `b : U' ⟶ U` of the presenting scheme in `𝓘_Z|_U` it is the isomorphism
`𝒪_{U'}(1) ≅ 𝓘·𝒪_{U'}` of Stacks 02OS (3) followed by the inclusion of the ideal sheaf into
`𝒪_{U'}`, which on the standard chart at `a ∈ 𝓘(V)` is `t ↦ (t / a⁽¹⁾) · b^♯(a)`, the map
induced by the shift `A(1) ⟶ A` of the Rees algebra
(`AlgebraicGeometry.incl_app_twistOneIsoExceptionalIdealModule_hom`); here it is read on `P_U`
through the comparison `Stacks.Blowup.reesSituationBlowUpIso` of the two Rees constructions.  It
does not involve the exceptional divisor `E` of the blowup of the algebraic space. -/
def blowUpChartTwistOneToUnit :
    blowUpChartTwistOne Z P hcU hcR heq ⟶ SheafOfModules.unit
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj (reesGlueingData (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR heq).projChart).toSheafedSpace) :=
  (RingedSpaceModuleAdjunction.modulePullback (Stacks.Blowup.reesSituationBlowUpIso
      (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
        P)).hom.toLRSHom.toShHom).map
      ((AlgebraicGeometry.twistOneIsoExceptionalIdealModule
          (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)).hom ≫
        Stacks.CartierAffineLocal.incl (AlgebraicGeometry.exceptionalIdeal
          (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P))) ≫
    (Stacks.IdealSheafRestrict.pullbackUnitIso
      (Stacks.Blowup.reesSituationBlowUpIso
        (reesChartIdeal (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z) P)).hom).hom

/-- **G3 carried to `P_U`: the identification `𝒪_{P_U}(1) ≅ 𝓘(E ×_{X'} P_U)` is the canonical
map `𝒪(1) ⟶ 𝒪`.**  `AlgebraicGeometry.Space.blowUpChartTwistOneIsoIdealSheaf` followed by the
inclusion of the ideal sheaf of `E ×_{X'} P_U ⟶ P_U` into `𝒪_{P_U}` is
`AlgebraicGeometry.Space.blowUpChartTwistOneToUnit`: the pullback, along the comparison
`Stacks.Blowup.reesSituationBlowUpIso`, of the isomorphism of Stacks 02OS (3) followed by the
inclusion into `𝒪`. -/
theorem blowUpChartTwistOneIsoIdealSheaf_hom_comp_ι :
    isoIdealSheafToUnit ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart)) (blowUpChartTwistOneIsoIdealSheaf Z P hcU hcR heq) =
      blowUpChartTwistOneToUnit Z P hcU hcR heq :=
  isoIdealSheafToUnit_mapIso_trans_idealSheafIsoPullbackOfSquare_symm _ _ _ _ _ _


/-- **G2 at the atlas of the blowup.**  The map `c : 𝒪_{P_U}(1)^a ⟶ φ^*𝒪_{X'}` of the descent
(`AlgebraicGeometry.Space.blowUpChartTwistOneAssociatedIso` followed by `φ^*` of the inclusion
`𝓘_E ⟶ 𝒪_{X'}`) is computed on `P_U` by `AlgebraicGeometry.Space.blowUpChartTwistOneIsoIdealSheaf`
followed by the inclusion `κ` of the ideal sheaf of `E ×_{X'} P_U ⟶ P_U` into `𝒪_{P_U}`
(`AlgebraicGeometry.Space.isoIdealSheafToUnit`):
`c = (blowUpChartTwistOneIsoIdealSheaf ≫ κ)^a ≫ u⁻¹`, with `u` the identification
`AlgebraicGeometry.Space.modulePullbackPresentationAtlasUnitIso`, which is
`AlgebraicGeometry.Space.modulePullbackChartToSpaceUnitIso` at
`AlgebraicGeometry.Space.presentationChart`.  It is
`AlgebraicGeometry.Space.modulePullbackChartToSpaceDefiningIdealIso_hom_comp` at the atlas. -/
theorem blowUpAtlasMapComputes_idealSheaf :
    AtlasMapComputes (blowUpPresentation Z P hcU hcR heq)
      (definingIdealSheaf B S hS (blowUpAlong Z P hcU hcR heq)
        (exceptionalDivisor Z P hcU hcR heq)).ι
      (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq)
      (isoIdealSheafToUnit ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart)) (blowUpChartTwistOneIsoIdealSheaf Z P hcU hcR heq)) :=
  atlasMapComputes_definingIdealSheaf (X := blowUpAlong Z P hcU hcR heq)
    (exceptionalDivisor Z P hcU hcR heq) (blowUpPresentation Z P hcU hcR heq)
    ((BigFppfOver.toScheme B S hS).map
          ((exceptionalDivisor Z P hcU hcR heq).2.2.rep.snd
            (reesGlueingData (centreIdeal Z) (isCartesianOnAffineCharts_centreIdeal Z)
              P hcU hcR heq).chart)) rfl
    (blowUpChartTwistOneIsoIdealSheaf Z P hcU hcR heq)
    (modulePullbackBlowUpAtlasExceptionalIdealIso Z P hcU hcR heq) HEq.rfl

/-- **The map `c` of the descent is the canonical map `𝒪(1) ⟶ 𝒪`.**  G2 and G3 combined:
`c = (blowUpChartTwistOneToUnit)^a ≫ u⁻¹`, which involves neither `E` nor `𝓘_E`. -/
theorem blowUpAtlasMapComputes_toUnit :
    AtlasMapComputes (blowUpPresentation Z P hcU hcR heq)
      (definingIdealSheaf B S hS (blowUpAlong Z P hcU hcR heq)
        (exceptionalDivisor Z P hcU hcR heq)).ι
      (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq)
      (blowUpChartTwistOneToUnit Z P hcU hcR heq) :=
  (blowUpAtlasMapComputes_idealSheaf Z P hcU hcR heq).of_eq
    (blowUpChartTwistOneIsoIdealSheaf_hom_comp_ι Z P hcU hcR heq)

/-- **The descended `𝒪_{X'}(1)` is characterised without reference to `E`.**  A morphism
`β : t^*𝒪_{P_U}(1)^a ⟶ s^*𝒪_{P_U}(1)^a` is the transition `α'` of
`AlgebraicGeometry.Space.blowUpTwistDescentDatum`, from which `𝒪_{X'}(1)` is descended, if and
only if it is compatible (`AlgebraicGeometry.Space.TransitionCompatible`) with the canonical
descent datum of `𝒪_{X'}` and the map `c = (blowUpChartTwistOneToUnit)^a ≫ u⁻¹`
(`AlgebraicGeometry.Space.presentationUnitMap`), that is `β ≫ s^*c = t^*c ≫ α_𝒪`.  Here
`AlgebraicGeometry.Space.blowUpChartTwistOneToUnit` is the canonical map `𝒪_{P_U}(1) ⟶ 𝒪_{P_U}`,
on charts `t ↦ (t / a⁽¹⁾) · b^♯(a)`, and `u : φ^*𝒪_{X'} ≅ 𝒪_{P_U}^a` is
`AlgebraicGeometry.Space.modulePullbackPresentationAtlasUnitIso`, built from `𝒪` alone: neither
involves `E` or `𝓘_E`. -/
theorem eq_blowUpTwistDescentDatum_alpha_iff
    (β : (modulePullback B S hS
          (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)).target).obj
          (blowUpChartTwistOneQcoh Z P hcU hcR heq).obj ⟶
        (modulePullback B S hS
          (presentationGroupoid (blowUpPresentation Z P hcU hcR heq)).source).obj
          (blowUpChartTwistOneQcoh Z P hcU hcR heq).obj) :
    β = (blowUpTwistDescentDatum Z P hcU hcR heq).alpha ↔
      TransitionCompatible (presentationAtlas (blowUpPresentation Z P hcU hcR heq))
        (presentationAtlas_comm (blowUpPresentation Z P hcU hcR heq))
        (SheafOfModules.unit (structureRingSheaf B S hS (blowUpAlong Z P hcU hcR heq)))
        (presentationUnitMap (blowUpPresentation Z P hcU hcR heq)
          (blowUpChartTwistOneToUnit Z P hcU hcR heq))
        β := by
  have key := fun β' => spaceBaseCompatible_iff_transitionCompatible
    (presentationAtlas (blowUpPresentation Z P hcU hcR heq))
    (presentationAtlas_comm (blowUpPresentation Z P hcU hcR heq))
    (exceptionalIdealQcohι Z P hcU hcR heq) (blowUpChartTwistOneQcoh Z P hcU hcR heq)
    (blowUpChartTwistOneAssociatedIso Z P hcU hcR heq)
    (blowUpAtlasMapComputes_toUnit Z P hcU hcR heq).comm β'
  constructor
  · rintro rfl
    exact (key _).1 (blowUpTwistCompatible_alpha Z P hcU hcR heq)
  · intro h
    exact eq_blowUpTwistDescentDatum_alpha Z P hcU hcR heq β ((key β).2 h)

end Blowup

section Canonical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : AlgebraicSpaces B S hS} [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **Stacks 085T, part (3): the canonical isomorphism `𝒪_{X'}(-1) ≅ 𝒪_{X'}(E)`.**  Let
`b : X' ⟶ X` be the blowing up of an algebraic space `X` along a closed subspace `Z` (Stacks
085Q, `AlgebraicGeometry.Space.blowUpAlong'`, with the equivalence-relation field of its descent
datum discharged by `AlgebraicGeometry.Space.isEquivalenceRelation_post_reesProj`), with
exceptional divisor `E = b⁻¹(Z)`, an effective Cartier divisor by part (2).  Then the twisting
sheaf `𝒪_{X'}(-1)` is isomorphic to the invertible sheaf `𝒪_{X'}(E)` of Stacks 0841 (1).

Here `𝒪_{X'}(n)` is the `n`th tensor power (Stacks 01CU) of the invertible sheaf `𝒪_{X'}(1)`
obtained by descending, along the étale presentation `P_R ⇉ P_U` of `X'` and the equivalence of
Stacks 03M3, the twisting sheaf `𝒪_{P_U}(1)` of the blowup `P_U` of the presenting scheme `U` in
`𝓘_Z|_U`, with transition morphism `α'` (`AlgebraicGeometry.Space.blowUpTwistDescentDatum`).

**Why the isomorphism is canonical.**  The descent datum of `𝒪_{X'}(1)` is characterised
without reference to `E` (`AlgebraicGeometry.Space.eq_blowUpTwistDescentDatum_alpha_iff`): a
morphism `β : t^*𝒪_{P_U}(1)^a ⟶ s^*𝒪_{P_U}(1)^a` is the transition `α'` if and only if
`β ≫ s^*c = t^*c ≫ α_𝒪`, where `α_𝒪` is the canonical descent datum of `𝒪_{X'}` and
`c = (blowUpChartTwistOneToUnit)^a ≫ u⁻¹`, built from the canonical map `𝒪(1) ⟶ 𝒪` of the
scheme blowup `P_U` (`AlgebraicGeometry.Space.blowUpChartTwistOneToUnit`: Stacks 02OS (3)
followed by the inclusion into `𝒪`, which on the standard chart at `a ∈ 𝓘(U)` is
`t ↦ (t / a⁽¹⁾) · b^♯(a)`, the map induced by the shift `A(1) ⟶ A` of the Rees algebra,
`AlgebraicGeometry.incl_app_twistOneIsoExceptionalIdealModule_hom`) and the identification
`u : φ^*𝒪_{X'} ≅ 𝒪_{P_U}^a` of `AlgebraicGeometry.Space.modulePullbackPresentationAtlasUnitIso`,
built from `𝒪` alone.  That lemma combines the uniqueness of the transition
(`AlgebraicGeometry.Space.eq_blowUpTwistDescentDatum_alpha`), its computation at the atlas
(`AlgebraicGeometry.Space.blowUpAtlasMapComputes_idealSheaf`) and on the chart
(`AlgebraicGeometry.Space.blowUpChartTwistOneIsoIdealSheaf_hom_comp_ι`).  So `𝒪_{X'}(1)` is the
descent of `𝒪_{P_U}(1)` along the unique datum compatible with `𝒪(1) ⟶ 𝒪`, and the isomorphism
below is `AlgebraicGeometry.Space.blowUpTwistSpaceNegOneIso`, the inverse of the descended
`𝒪_{X'}(1) ≅ 𝓘_E` of Stacks 02OS (3).

The parameters `hcU`, `hcR` and `hcRR` are the containment conditions on the big fppf site under
which the relative `Proj`s of the blowup are objects of the site. -/
@[stacks 085T "part (3): the canonical isomorphism O_{X'}(-1) = O_{X'}(E) on the blowup of an \
algebraic space, O_{X'}(1) being descended along the unique transition compatible with the \
canonical map O(1) → O", ega "II 8.1.8" "partial"]
def blowUpTwistSpaceNegOneIsoAssociatedInvertibleSheaf (Z : ClosedSubspaces B S hS X.obj)
    (P : Presentation B S hS X.obj X.property)
    (hcU : B.Contains (reesChartSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcR : B.Contains (reesRelationSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj)
    (hcRR : B.Contains (reesDoubleSituation (centreIdeal Z)
      (isCartesianOnAffineCharts_centreIdeal Z) P).relativeProj) :
    blowUpTwistSpace Z P hcU hcR (isEquivalenceRelation_post_reesProj (centreIdeal Z)
        (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR) (-1) ≅
      associatedInvertibleSheaf B S hS (blowUpAlong Z P hcU hcR
          (isEquivalenceRelation_post_reesProj (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR))
        (exceptionalDivisor Z P hcU hcR (isEquivalenceRelation_post_reesProj (centreIdeal Z)
          (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR))
        (isEffectiveCartierDivisor_exceptionalDivisor_blowUpAlong Z P hcU hcR
          (isEquivalenceRelation_post_reesProj (centreIdeal Z)
            (isCartesianOnAffineCharts_centreIdeal Z) P hcU hcR hcRR)) :=
  blowUpTwistSpaceNegOneIso Z P hcU hcR _

end Canonical

end AlgebraicGeometry.Space

end
