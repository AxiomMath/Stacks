module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence

/-!
# Finite presentation of the first cohomology sheaf above the pseudo-coherence cutoff

Let `X` be a ringed space and let `K` be an `m`-pseudo-coherent object of the derived category of
`𝒪_X`-modules whose cohomology sheaves vanish in every degree above `m + 1`. Stacks 08DN(2) says
that `H^{m+1}(K)` is an `𝒪_X`-module of finite presentation; that is the main result of this file.

Part (1) of the same lemma — that `H^m(K)` is of finite type when the cohomology vanishes above `m`
— is `AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom`.

## Main results

* `SheafOfModules.exists_isFinite_presentation_cokernel_of_retract`: the cokernel of a morphism
  between retracts of free modules on finite index types is finitely presented.
* `SheafOfModules.exists_isFinite_presentation_map`: a finite presentation carried along a
  colimit-preserving functor which matches the two unit sheaves of modules.
* `AlgebraicGeometry.RingedSpace.exists_isFinite_presentation_over_of_restrictModules`: a finite
  presentation on an open subspace read in the slice idiom.
* `AlgebraicGeometry.RingedSpace.isFinitePresentation_of_exists_local_presentation`: finite
  presentation is local on `X`.
* `AlgebraicGeometry.RingedSpace.isFinitePresentation_homology_of_isPseudoCoherentFrom`:
  **Stacks 08DN(2)**.

## Implementation notes

The Stacks proof of (2) first replaces the strictly perfect approximation `𝒫 ⟶ E|_U` by one with
`𝒫^i = 0` for `i > m + 1`, using Stacks 08C6 and a descending induction on the top nonvanishing
degree, after which `H^{m+1}(𝒫) = \Coker(𝒫^m \to 𝒫^{m+1})` with both terms direct summands of
finite free modules.

That truncation is not carried out here. Instead `H^{m+1}(𝒫)` is presented as the cokernel of
`𝒫^m \to Z^{m+1}(𝒫)`, which it is for any complex
(`HomologicalComplex.homologyIsCokernel`): the source is a direct summand of a finite free module
because `𝒫` is strictly perfect, and the target becomes one after restriction to a smaller open
subspace of `X` by
`AlgebraicGeometry.RingedSpace.exists_isDirectSummandOfFiniteFree_restrict_cycles`, which is the
same lemma that part (1) uses and is where the vanishing of the cohomology above `m + 1` enters.
Restriction to a smaller open subspace preserves finite colimits, so it takes that cokernel to the
cokernel of the restricted morphism.

Presenting the cokernel finitely is the one genuinely new piece of algebra:
`SheafOfModules.exists_isFinite_presentation_cokernel_of_retract` takes the generators from the
retraction `𝒪^{⊕n} \to B` and the relations from two families — the image of the morphism, read
through the retraction of the source, and the complement `1 - r \circ i` of the idempotent cutting
`B` out of `𝒪^{⊕n}`.

Two idioms meet. `SheafOfModules.IsFinitePresentation` asks for presentations of `ℱ.over W` for
opens `W` of `X` — the slice idiom — while the cokernel above lives on the open subspace
`X.restrict W.isOpenEmbedding`. The bridge is `TopologicalSpace.Opens.sheafOfModulesEquivOver`,
whose inverse preserves colimits and matches the two unit sheaves of modules, so
`SheafOfModules.Presentation.map` carries the presentation across. That transport is stated in
`SheafOfModules.exists_isFinite_presentation_map`, whose binders are literally
`SheafOfModules.{u} R` and `SheafOfModules.{u} S`: the ring of the open subspace is spelled `𝒪_W`
on one side of the equivalence and `W.sheafRestrict.obj 𝒪_X` on the other, and typeclass
resolution, which unfolds only at reducible transparency, cannot identify the two. Fixing the
categories in the binders makes the `PreservesColimitsOfSize` instance be synthesized at the
functor's own type, after which only term-level unification is left at the point of use.

All universes coincide: `StrictlyPerfect.OXMod` is only defined when the ring universe and the
space universe of the ringed space agree.

## References

* [The Stacks Project, Lemma 20.47.4 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [The Stacks Project, Lemma 20.46.3 (08C6)](https://stacks.math.columbia.edu/tag/08C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect AlgebraicGeometry

namespace SheafOfModules

universe u v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- A finite presentation transported along an isomorphism of sheaves of modules. -/
public theorem exists_isFinite_presentation_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    (h : ∃ p : M.Presentation, p.IsFinite) : ∃ p : N.Presentation, p.IsFinite := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.ofIsIso e.hom, inferInstance⟩

/-- A finite presentation carried along a colimit-preserving functor which matches the two unit
sheaves of modules. -/
public theorem exists_isFinite_presentation_map {C' : Type*} [Category C']
    {J' : GrothendieckTopology C'} {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
    [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S) [PreservesColimitsOfSize.{u, u} F]
    (η : unit S ≅ F.obj (unit R)) {M : SheafOfModules.{u} R}
    (h : ∃ p : M.Presentation, p.IsFinite) : ∃ p : (F.obj M).Presentation, p.IsFinite := by
  obtain ⟨p, hp⟩ := h
  have hgen : Finite p.generators.I := hp.isFiniteType_generators.finite
  have hrel : Finite p.relations.I := hp.isFiniteType_relations.finite
  exact ⟨p.map F η,
    { isFiniteType_generators := ⟨by simpa only [Presentation.map_generators_I] using hgen⟩
      isFiniteType_relations := ⟨by simpa only [Presentation.map_relations_I] using hrel⟩ }⟩

/-- **The cokernel of a morphism between direct summands of finite free modules is finitely
presented.** If `A` is a retract of the free module on a finite index type `K` and `B` is a retract
of the free module on a finite index type `I`, then the cokernel of any `f : A ⟶ B` admits a finite
presentation. -/
public theorem exists_isFinite_presentation_cokernel_of_retract {A B : SheafOfModules.{u} R}
    {I K : Type u} [Finite I] [Finite K] (a : Retract A (free (R := R) K))
    (b : Retract B (free (R := R) I)) (f : A ⟶ B) :
    ∃ p : (cokernel f).Presentation, p.IsFinite := by
  let h₁ : free (R := R) K ⟶ free (R := R) I := a.r ≫ f ≫ b.i
  let h₂ : free (R := R) I ⟶ free (R := R) I := 𝟙 _ - b.r ≫ b.i
  let h : free (R := R) (K ⊕ I) ⟶ free (R := R) I :=
    (freeSumIso (R := R) K I).inv ≫ coprod.desc h₁ h₂
  let g : free (R := R) I ⟶ cokernel f := b.r ≫ cokernel.π f
  have hcg : coprod.desc h₁ h₂ ≫ g = 0 := by
    refine coprod.hom_ext ?_ ?_
    · rw [coprod.inl_desc_assoc, comp_zero]
      change (a.r ≫ f ≫ b.i) ≫ b.r ≫ cokernel.π f = 0
      rw [Category.assoc, Category.assoc, ← Category.assoc b.i b.r, b.retract, Category.id_comp,
        cokernel.condition, comp_zero]
    · rw [coprod.inr_desc_assoc, comp_zero]
      change (𝟙 _ - b.r ≫ b.i) ≫ b.r ≫ cokernel.π f = 0
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
        ← Category.assoc b.i b.r, b.retract, Category.id_comp, sub_self]
  have hg : h ≫ g = 0 := by
    change (freeSumIso (R := R) K I).inv ≫ coprod.desc h₁ h₂ ≫ g = 0
    rw [hcg, comp_zero]
  have hdesc {Z : SheafOfModules.{u} R} (k : free (R := R) I ⟶ Z) (hk : h ≫ k = 0) :
      coprod.desc h₁ h₂ ≫ k = 0 :=
    (cancel_epi (freeSumIso (R := R) K I).inv).1 (by simpa [h, Category.assoc] using hk)
  have hfk_of {Z : SheafOfModules.{u} R} (k : free (R := R) I ⟶ Z) (hk : h ≫ k = 0) :
      f ≫ b.i ≫ k = 0 := by
    refine (cancel_epi a.r).1 ?_
    have hh : coprod.inl ≫ coprod.desc h₁ h₂ ≫ k = 0 := by rw [hdesc k hk, comp_zero]
    rw [coprod.inl_desc_assoc] at hh
    simpa [h₁] using hh
  have hfactor {Z : SheafOfModules.{u} R} (k : free (R := R) I ⟶ Z) (hk : h ≫ k = 0) :
      k = b.r ≫ b.i ≫ k := by
    have hr : coprod.inr ≫ coprod.desc h₁ h₂ ≫ k = 0 := by rw [hdesc k hk, comp_zero]
    rw [coprod.inr_desc_assoc] at hr
    change (𝟙 _ - b.r ≫ b.i) ≫ k = 0 at hr
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc] at hr
    exact sub_eq_zero.mp hr
  have hcol : IsColimit (CokernelCofork.ofπ g hg) :=
    CokernelCofork.IsColimit.ofπ g hg
      (fun {_} k hk => cokernel.desc f (b.i ≫ k) (hfk_of k hk))
      (by
        intro Z k hk
        dsimp [g]
        rw [Category.assoc, cokernel.π_desc]
        exact (hfactor k hk).symm)
      (by
        intro Z k hk m hm
        apply (cancel_epi g).1
        calc
          g ≫ m = k := hm
          _ = g ≫ cokernel.desc f (b.i ≫ k) (hfk_of k hk) := by
            dsimp [g]
            rw [Category.assoc, cokernel.π_desc]
            exact hfactor k hk)
  refine ⟨presentationOfIsCokernelFree h g hg hcol, ?_, ?_⟩
  · exact ⟨by simpa [presentationOfIsCokernelFree, generatorsOfIsCokernelFree] using
      (inferInstance : Finite I)⟩
  · exact ⟨by simpa [presentationOfIsCokernelFree, relationsOfIsCokernelFree,
      generatorsOfIsCokernelFree] using (inferInstance : Finite (K ⊕ I))⟩

end SheafOfModules

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- **The cokernel of a morphism of direct summands of finite free `𝒪_Y`-modules is finitely
presented.** -/
public theorem exists_isFinite_presentation_cokernel_of_isDirectSummandOfFiniteFree
    {Y : RingedSpace.{u, u}} {A B : OXMod.{u, u} Y} (hA : IsDirectSummandOfFiniteFree A)
    (hB : IsDirectSummandOfFiniteFree B) (f : A ⟶ B) :
    ∃ p : (cokernel f).Presentation, p.IsFinite := by
  obtain ⟨n, ⟨ρA⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hA
  obtain ⟨k, ⟨ρB⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hB
  exact SheafOfModules.exists_isFinite_presentation_cokernel_of_retract
    (ρA.trans (Retract.ofIso (finiteFreeIsoFree Y n)))
    (ρB.trans (Retract.ofIso (finiteFreeIsoFree Y k))) f

/-- The inverse of the equivalence between sheaves of modules over the slice `Over W` and
`𝒪`-modules on the open subspace `W` takes the structure module of `W` to the unit sheaf of
modules over the slice. -/
public def equivOverUnitInvIso (X : RingedSpace.{u, u}) (W : Opens X.carrier) :
    SheafOfModules.unit ((structureSheafOfRings X).over W) ≅
      (W.sheafOfModulesEquivOver (structureSheafOfRings X)).inverse.obj
        (SheafOfModules.unit (structureSheafOfRings (X.restrict W.isOpenEmbedding))) :=
  (W.sheafOfModulesEquivOver (structureSheafOfRings X)).unitIso.app _ ≪≫
    (W.sheafOfModulesEquivOver (structureSheafOfRings X)).inverse.mapIso
      (equivOverUnitIso X W).symm

/-- A finite presentation of the restriction of an `𝒪_X`-module to an open subspace `W` is a
finite presentation of its restriction to the slice `Over W`, which is the idiom in which
`SheafOfModules.IsFinitePresentation` is phrased. -/
public theorem exists_isFinite_presentation_over_of_restrictModules (M : OXMod.{u, u} X)
    (W : Opens X.carrier) (h : ∃ p : ((restrictModules X W).obj M).Presentation, p.IsFinite) :
    ∃ p : (M.over W).Presentation, p.IsFinite := by
  have eTgt : (W.sheafOfModulesEquivOver (structureSheafOfRings X)).inverse.obj
      ((restrictModules X W).obj M) ≅ M.over W :=
    (W.sheafOfModulesEquivOver (structureSheafOfRings X)).inverse.mapIso
        ((restrictModulesIsoOverComp X W).symm.app M) ≪≫
      ((W.sheafOfModulesEquivOver (structureSheafOfRings X)).unitIso.app (M.over W)).symm
  exact SheafOfModules.exists_isFinite_presentation_of_iso eTgt
    (SheafOfModules.exists_isFinite_presentation_map
      (W.sheafOfModulesEquivOver (structureSheafOfRings X)).inverse
      (equivOverUnitInvIso X W) h)

/-- The quasi-coherent data of an `𝒪_X`-module presented over an open neighbourhood `W x` of each
point `x` of `X`, the covering of `X` being indexed by the points of `X`. -/
public def quasicoherentDataOfLocalPresentation (M : OXMod.{u, u} X)
    (W : X.carrier → Opens X.carrier) (hxW : ∀ x, x ∈ W x)
    (p : ∀ x : X.carrier, (M.over (W x)).Presentation) :
    SheafOfModules.QuasicoherentData.{u, u, u, u} M where
  I := (X.carrier : Type u)
  X := W
  coversTop := (Opens.coversTop_iff (X.carrier : Type u) W).mpr
    (TopologicalSpace.IsOpenCover.mk
      (Opens.ext (Set.eq_univ_of_forall fun x => (Opens.mem_iSup (s := W)).2 ⟨x, hxW x⟩)))
  presentation := p

/-- An `𝒪_X`-module which admits, near every point of `X`, a finite presentation of its
restriction to the slice over an open neighbourhood is of finite presentation. -/
public theorem isFinitePresentation_of_exists_local_presentation (M : OXMod.{u, u} X)
    (h : ∀ x : X.carrier, ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ p : (M.over W).Presentation, p.IsFinite) :
    SheafOfModules.IsFinitePresentation (R := structureSheafOfRings X) M := by
  classical
  choose W hxW p hp using h
  have hq : (quasicoherentDataOfLocalPresentation M W hxW p).IsFinitePresentation := by
    constructor
    intro x
    exact hp x
  constructor
  refine ⟨quasicoherentDataOfLocalPresentation M W hxW p, ?_⟩
  exact hq

/-- Let `X` be a ringed space and let `K` be an `m`-pseudo-coherent object of the derived category
of `𝒪_X`-modules with `H^i(K) = 0` for `i > m + 1`. Then `H^{m+1}(K)` is an `𝒪_X`-module of finite
presentation. -/
@[stacks 08DN "part (2)"]
public theorem isFinitePresentation_homology_of_isPseudoCoherentFrom
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (K : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, m + 1 < i →
      IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj K)) :
    SheafOfModules.IsFinitePresentation (R := structureSheafOfRings X)
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) (m + 1)).obj K) := by
  obtain ⟨E, hE, ⟨eK⟩⟩ := hK
  have eEK : ∀ i : ℤ, E.homology i ≅
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj K := fun i =>
    (derivedHomologyIso E i).symm ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso eK
  have hvanishE : ∀ i : ℤ, m + 1 < i → IsZero (E.homology i) := fun i hi =>
    IsZero.of_iso (hvanish i hi) (eEK i)
  refine isFinitePresentation_of_exists_local_presentation _ fun x => ?_
  obtain ⟨U, hxU, P, hP, α, hα, -⟩ := hE x
  have hPzero : ∀ i : ℤ, m + 1 < i → IsZero (P.homology i) := fun i hi =>
    IsZero.of_iso ((restrictModules X U).map_isZero (hvanishE i hi))
      (@asIso _ _ _ _ _ (hα i (by omega)) ≪≫ restrictComplexHomologyIso E U i)
  obtain ⟨W, hWU, hxW, hZ⟩ :=
    exists_isDirectSummandOfFiniteFree_restrict_cycles hP (m + 1) hPzero hxU
  refine ⟨W, hxW, ?_⟩
  set G := restrictModulesOfLE X hWU with hGdef
  have hXm : IsDirectSummandOfFiniteFree (G.obj (P.X m)) :=
    isDirectSummandOfFiniteFree_restrictModulesOfLE hWU (hP.directSummand m)
  obtain ⟨q, hq⟩ := exists_isFinite_presentation_cokernel_of_isDirectSummandOfFiniteFree
    hXm hZ (G.map (P.toCycles m (m + 1)))
  have hprev : (ComplexShape.up ℤ).prev (m + 1) = m := by rw [CochainComplex.prev]; omega
  have hcokP : cokernel (P.toCycles m (m + 1)) ≅ P.homology (m + 1) :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (P.toCycles m (m + 1)))
      (P.homologyIsCokernel m (m + 1) hprev)
  have hcokG : cokernel (G.map (P.toCycles m (m + 1))) ≅ G.obj (P.homology (m + 1)) :=
    (PreservesCokernel.iso G (P.toCycles m (m + 1))).symm ≪≫ G.mapIso hcokP
  have : IsIso (HomologicalComplex.homologyMap α (m + 1)) := hα (m + 1) (by omega)
  have eFin : G.obj (P.homology (m + 1)) ≅ (restrictModules X W).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) (m + 1)).obj K) :=
    G.mapIso (asIso (HomologicalComplex.homologyMap α (m + 1))) ≪≫
      G.mapIso (restrictComplexHomologyIso E U (m + 1)) ≪≫
      (restrictModulesOfLECompIso X hWU).app (E.homology (m + 1)) ≪≫
      (restrictModules X W).mapIso (eEK (m + 1))
  exact exists_isFinite_presentation_over_of_restrictModules _ W
    (SheafOfModules.exists_isFinite_presentation_of_iso (hcokG ≪≫ eFin) ⟨q, hq⟩)

end AlgebraicGeometry.RingedSpace

end
