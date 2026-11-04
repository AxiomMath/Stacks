module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.TransverseBaseChangeArrow
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreePullbackIdentity
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechClassPassage
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassSpellings

/-!
# The class map of Stacks 0G7Q commutes with base change, for every number of equations

Let `g : Y' ⟶ Y` be a morphism of schemes, let `f₁, …, f_c ∈ Γ(Y, 𝒪_Y)` — **any number of them,
`c = 0` included** — with pulled-back equations `f'ⱼ = g^♯(fⱼ)`, and let `ℱ` be a quasi-coherent
`𝒪_Y`-module.  Write `Z` for the common zero locus of the `fⱼ` and `Z' = g⁻¹(Z)`, which is the
common zero locus of the `f'ⱼ`.  The class maps `c_{f₁,…,f_c} : ℱ ⟶ i_*ℋ^c_Z(ℱ)` of
[Stacks, Tag 0G7Q] (`Stacks.Perfect.FractionClass.classMapToSupport`, the spelling available at
every `c`) commute with base change:

`g^*(c_{f₁,…,f_c})` followed by the degree-`c` reading of the arrow of [Stacks, Tag 0G78]
`= c_{f'₁,…,f'_c}`,

where the arrow of [Stacks, Tag 0G78] in degree `c` is `Stacks.Gysin.supportedBaseChangePull` at
the down arrow `Lg^*ℱ ⟶ g^*ℱ`, and an `eqToHom` moves between the two spellings of `Z'`.  This is
the first diagram of [Stacks, Tag 0G7U] in the shape [Stacks, Tag 0G89] consumes it.

## Main results

* `Stacks.Gysin.classMapToSupport_baseChange`: the statement above.
* `Stacks.Gysin.isLE_supportPush_equationsClosedSet`: `i_*R𝓗_Z(ℱ)` has no cohomology above degree
  `c`, which is the hypothesis `hLE` the degree-`c` arrow is defined under.
* `Stacks.Gysin.pullback_classMap_comp_mapHomology_comp_homologyMap`: the Čech-level statement —
  the pulled-back class of the fraction, carried by the comparison `g^*Hᶜ ⟶ Hᶜ g^*` and by the map
  of Čech complexes, is the class of the pulled-back fraction.
* `Stacks.Gysin.homology_supportedBaseChangeDerived`: the degree-`c` cohomology of the arrow of
  [Stacks, Tag 0G78], computed on the Čech complexes from the derived diagram of
  [Stacks, Tag 0G7U] (`Stacks.Perfect.CechDerivedBaseChange.derivedBaseChangeSquare_cech`).
* `Stacks.Gysin.pullback_cechClass_comp_topDegree_inv`: the top-degree comparison
  `Hᶜ(Lg^*K) ≅ g^*Hᶜ(K)` read on the Čech representative of `K = i_*R𝓗_Z(ℱ)`; it is
  `Stacks.AlgebraicGeometry.TopDegreeBaseChange.representativeClass_comp_eq_mapHomology` with the
  representative's two comparisons unfolded by `classOfRepresentative_quotientCompQhIso` and
  `comparisonOfRepresentative_quotientCompQhIso`.

## Implementation notes

**No case split on `c`.**  Every input is stated for an arbitrary family: the derived square
`derivedBaseChangeSquare_cech`, the base change of the fraction
`Stacks.Perfect.CechFractionBaseChange.cplxBaseChange_comp_fracTermTop`, the class map
`classMapToSupport` and the top-degree comparison.  In particular the cokernel of the last Čech
differential, which exists only for `c ≥ 1` and through which
`Stacks.Perfect.CechDegreeCBaseChange.supportedFractionSource_baseChange` goes, is not used.

**The hypothesis `hLE`.**  The degree-`c` arrow `supportedBaseChangePull` is only defined given
`hLE`; the statement takes it as an argument because the arrow does, and
`isLE_supportPush_equationsClosedSet` proves it.  It is a proposition, so its proof does not
enter the statement.

**Rearrangements at a variable category.**  The objects cross the spellings `Y.Modules` and
`SheafOfModules (structureSheafRing Y.toRingedSpace)`, and `Scheme.Modules.pullback g` and
`modulePullback g.toLRSHom.toShHom`, which are definitionally equal but on which `rw` refuses to
fire; every reassociation is done by a `private` lemma at a variable category, applied with
`exact`, as in `Stacks.Perfect.CechDegreeCBaseChange`.

No `@[stacks]` attribute is attached here.

## References

* [Stacks Project, Tag 0G7U](https://stacks.math.columbia.edu/tag/0G7U)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G78](https://stacks.math.columbia.edu/tag/0G78)
* [Stacks Project, Tag 0G89](https://stacks.math.columbia.edu/tag/0G89)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet isClosed_equationsClosedSet)
open Stacks.Perfect.SupportedFraction (supportPush supportPushSingle supportCohomologySheaf
  cechToDerivedSupport cechToSupport isIso_cechToSupport derivedQHomologyIso)
open Stacks.Perfect.SupportedDerivedBaseChange (equationsClosedSet_pullback
  isClosed_equationsClosedSet_pullback equationsClosedSet_pullback_subset supportedPullbackRoute)
open Stacks.Perfect.CechDegreeCBaseChange (supportPushSingle_congr)
open AlgebraicGeometry.RingedSpaceThickening (derivedPullbackSingleObj)

universe u

namespace Stacks.Gysin

section Representative

open _root_.DerivedCategory Stacks.RepresentativeHomology

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory D]

/-- Dropping an identity in the middle of a composite, at an abstract category. -/
private lemma id_middle_formal {E : Type*} [Category E] {A₀ A₁ B C₀ : E} (a : A₀ ⟶ A₁)
    (b : A₁ ⟶ B) (m : B ⟶ B) (d : B ⟶ C₀) (hm : m = 𝟙 B) :
    a ≫ b ≫ m ≫ d = a ≫ b ≫ d := by
  rw [hm, Category.id_comp]

/-- Congruence of a three-fold composite, at an abstract category. -/
private lemma congr_comp3_formal {E : Type*} [Category E] {A₀ A₁ A₂ A₃ : E}
    (a a' : A₀ ⟶ A₁) (b b' : A₁ ⟶ A₂) (d d' : A₂ ⟶ A₃) (ha : a = a') (hb : b = b')
    (hd : d = d') : a ≫ b ≫ d = a' ≫ b' ≫ d' := by
  rw [ha, hb, hd]

/-- Reading a square `ε ≫ θ = b ≫ q ≫ e`, with `ε` split by `ι`, through a functor, at abstract
categories. -/
private lemma derived_square_formal {E E' : Type*} [Category E] [Category E'] (H : E ⥤ E')
    {A₀ A A₁ A₂ B : E} (ι : A ⟶ A₀) (ε : A₀ ⟶ A) (θ : A ⟶ B) (b : A₀ ⟶ A₁) (q : A₁ ⟶ A₂)
    (e : A₂ ⟶ B) {H₀ H₁ : E'} (d : H.obj A₁ ⟶ H₀) (m : H₀ ⟶ H₁) (d' : H₁ ⟶ H.obj A₂)
    (hι : ι ≫ ε = 𝟙 A) (hsq : ε ≫ θ = (b ≫ q) ≫ e) (hq : H.map q = d ≫ m ≫ d') :
    H.map θ = H.map (ι ≫ b) ≫ d ≫ m ≫ d' ≫ H.map e := by
  have hθ : θ = ι ≫ b ≫ q ≫ e := by
    rw [← Category.id_comp θ, ← hι, Category.assoc, hsq, Category.assoc]
  rw [hθ, H.map_comp, H.map_comp, H.map_comp, hq, H.map_comp]
  simp only [Category.assoc]

/-- The final chase of `classMapToSupport_baseChange`, at abstract categories. -/
private lemma final_chase_formal {E E' : Type*} [Category E] [Category E'] (G : E ⥤ E')
    {A₀ A₁ A₂ A₃ : E} {B₀ B₁ B₂ B₃ B₄ B₅ B₆ B₇ : E'} (x : A₀ ⟶ A₁) (y : A₁ ⟶ A₂) (w : A₂ ⟶ A₃)
    (t : G.obj A₃ ⟶ B₀) (h : B₀ ⟶ B₁) (z : B₁ ⟶ B₂) (p : B₀ ⟶ B₃) (d : B₃ ⟶ B₄)
    (m : B₄ ⟶ B₅) (d' : B₅ ⟶ B₆) (he : B₆ ⟶ B₁) (mH : G.obj A₂ ⟶ B₄) (x' : G.obj A₀ ⟶ B₇)
    (y' : B₇ ⟶ B₅) (hφ : B₆ ⟶ B₂)
    (hθ : h = p ≫ d ≫ m ≫ d' ≫ he) (e1 : G.map w ≫ t ≫ p ≫ d = mH)
    (e4 : G.map (x ≫ y) ≫ mH ≫ m = x' ≫ y') (e5 : he ≫ z = hφ) :
    G.map (x ≫ y ≫ w) ≫ (t ≫ h) ≫ z = x' ≫ y' ≫ d' ≫ hφ := by
  rw [hθ, ← e5, ← Category.assoc x' y', ← e4, ← e1, ← Category.assoc x y w, G.map_comp]
  simp only [Category.assoc]

/-- A functor preserves a composite equal to the identity, at abstract categories. -/
private lemma map_comp_eq_id_formal {E E' : Type*} [Category E] [Category E'] (H : E ⥤ E')
    {A B : E} (a : A ⟶ B) (b : B ⟶ A) (h : a ≫ b = 𝟙 A) : H.map a ≫ H.map b = 𝟙 _ := by
  rw [← H.map_comp, h, H.map_id]

/-- Cancelling an isomorphism and a split pair at the head of a composite, at an abstract
category. -/
private lemma head_cancel_formal {E : Type*} [Category E] {A B C₀ C₁ D₀ : E} (i : A ≅ B)
    (x : B ⟶ C₀) (m₁ : C₀ ⟶ C₁) (m₂ : C₁ ⟶ C₀) (y : C₀ ⟶ D₀) (hm : m₁ ≫ m₂ = 𝟙 C₀) :
    i.inv ≫ i.hom ≫ x ≫ m₁ ≫ m₂ ≫ y = x ≫ y := by
  rw [reassoc_of% hm, Iso.inv_hom_id_assoc]

/-- Cancelling an isomorphism at the tail of a composite, at an abstract category. -/
private lemma tail_cancel_formal {E : Type*} [Category E] {A₀ A₁ A₂ A₃ A₄ A₅ A₆ : E}
    (a : A₀ ⟶ A₁) (b : A₁ ⟶ A₂) (c : A₂ ⟶ A₃) (d : A₃ ⟶ A₄) (e : A₄ ⟶ A₅) (i : A₆ ≅ A₅) :
    a ≫ b ≫ c ≫ (d ≫ e ≫ i.inv) ≫ i.hom = a ≫ b ≫ c ≫ d ≫ e := by
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- `Stacks.RepresentativeHomology.classOfRepresentative` at the representative `Qh(P) ≅ Q(P) ≅ K`
given by an isomorphism `φ : Q(P) ⟶ K`: it is the identification of `Hᵃ(P)` with `Hᵃ(Q P)`
followed by `Hᵃ(φ)`. -/
theorem classOfRepresentative_quotientCompQhIso (P : CochainComplex C ℤ) {K : DerivedCategory C}
    (φ : Q.obj P ⟶ K) [hφ : IsIso φ] (a : ℤ) :
    classOfRepresentative P ((quotientCompQhIso C).app P ≪≫ asIso φ) a =
      (homologyFunctorFactors C a).inv.app P ≫ (homologyFunctor C a).map φ := by
  simp only [classOfRepresentative, homologyFunctorFactorsh_inv_app_quotient_obj, Iso.trans_hom,
    Iso.app_hom, asIso_hom, Functor.map_comp, Category.assoc]
  exact head_cancel_formal ((HomotopyCategory.homologyFunctorFactors C (ComplexShape.up ℤ) a).app P)
    _ _ _ _ (map_comp_eq_id_formal (homologyFunctor C a) _ _
      (Iso.inv_hom_id_app (quotientCompQhIso C) P))

/-- `Stacks.RepresentativeHomology.comparisonOfRepresentative` at the representative
`Qh(P) ≅ Q(P) ≅ K` given by an isomorphism `φ : Q(P) ⟶ K`, with the factorizations of the
cohomology functor through the homotopy category removed. -/
theorem comparisonOfRepresentative_quotientCompQhIso (G : C ⥤ D) [G.Additive]
    (L : DerivedCategory C ⥤ DerivedCategory D)
    (cmp : ∀ P : CochainComplex C ℤ,
      L.obj (Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj P)) ⟶
        Qh.obj ((HomotopyCategory.quotient D (ComplexShape.up ℤ)).obj
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)))
    (P : CochainComplex C ℤ) {K : DerivedCategory C} (φ : Q.obj P ⟶ K) [hφ : IsIso φ] (a : ℤ) :
    comparisonOfRepresentative G L cmp P ((quotientCompQhIso C).app P ≪≫ asIso φ) a =
      (homologyFunctor D a).map (L.map (asIso φ).inv ≫ L.map ((quotientCompQhIso C).inv.app P) ≫
          cmp P ≫ (quotientCompQhIso D).hom.app ((G.mapHomologicalComplex _).obj P)) ≫
        (homologyFunctorFactors D a).hom.app ((G.mapHomologicalComplex _).obj P) := by
  simp only [comparisonOfRepresentative, homologyFunctorFactorsh_hom_app_quotient_obj,
    Iso.trans_inv, Iso.app_inv, Functor.map_comp, Category.assoc]
  exact tail_cancel_formal _ _ _ _ _
    ((HomotopyCategory.homologyFunctorFactors D (ComplexShape.up ℤ) a).app
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))

end Representative

attribute [local instance 10000] HasDerivedCategory.standard

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) {c : ℕ} (f : Fin c → Γ(Y, ⊤)) (F : Y.Modules)

open Stacks.Perfect.ExtendedAlternatingCech (cplx)
open Stacks.Perfect.FractionClass (fracCycle fracTermTop classMap fracCycle_comp_iCycles)
open Stacks.Perfect.CechBaseChange (cplxBaseChange extendBaseChange)
open Stacks.Perfect.AbelianCechClassPassage (fracExtendCycles fracExtendCycles_comp_iCycles
  classExtendHomology classExtendHomology_eq)

/-- In degree `c`, the map of extended Čech complexes `g^*(ℱ^•) ⟶ (g^*ℱ)^•` carries the pulled-back
fraction to the fraction of the pulled-back equations.  This is
`Stacks.Perfect.CechFractionBaseChange.cplxBaseChange_comp_fracTermTop` read on the `ℤ`-graded
extensions. -/
theorem pullback_fracTermTop_comp_extendBaseChange_f :
    (Scheme.Modules.pullback g).map (fracTermTop f F ≫ ((cplx f F).extendXIso
        ComplexShape.embeddingUpNat (Stacks.Perfect.SupportedFraction.embeddingUpNat_f c)).inv) ≫
      (extendBaseChange g f F).f (c : ℤ) =
    fracTermTop (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) ≫
      ((cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).extendXIso
        ComplexShape.embeddingUpNat (Stacks.Perfect.SupportedFraction.embeddingUpNat_f c)).inv := by
  have hc := Stacks.Perfect.SupportedFraction.embeddingUpNat_f c
  have hinv : (Scheme.Modules.pullback g).map
        ((cplx f F).extendXIso ComplexShape.embeddingUpNat hc).inv =
      ((((Scheme.Modules.pullback g).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (cplx f F)).extendXIso ComplexShape.embeddingUpNat hc).inv ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g)
          (cplx f F) ComplexShape.embeddingUpNat).hom.f (c : ℤ) := by
    rw [HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ hc, Iso.inv_hom_id_assoc]
  have hcancel : (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g)
        (cplx f F) ComplexShape.embeddingUpNat).hom.f (c : ℤ) ≫
      (HomologicalComplex.mapHomologicalComplexExtendIso (Scheme.Modules.pullback g)
        (cplx f F) ComplexShape.embeddingUpNat).inv.f (c : ℤ) = 𝟙 _ := by
    rw [← HomologicalComplex.comp_f, Iso.hom_inv_id, HomologicalComplex.id_f]
  rw [extendBaseChange, HomologicalComplex.comp_f, HomologicalComplex.extendMap_f _ _ hc,
    (Scheme.Modules.pullback g).map_comp, hinv, Category.assoc, Category.assoc,
    reassoc_of% hcancel, Iso.inv_hom_id_assoc, ← Category.assoc,
    Stacks.Perfect.CechFractionBaseChange.cplxBaseChange_comp_fracTermTop]

/-- **The cycle of the fraction commutes with base change**: the pulled-back cycle, carried by the
comparison `g^*Zᶜ ⟶ Zᶜ g^*` and by the map of Čech complexes, is the cycle of the fraction of the
pulled-back equations. -/
theorem pullback_fracExtendCycles_comp_mapCycles_comp_cyclesMap :
    (Scheme.Modules.pullback g).map (fracExtendCycles f F) ≫
        Stacks.MapHomologyCycles.mapCycles (Scheme.Modules.pullback g)
          ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ) ≫
        HomologicalComplex.cyclesMap (extendBaseChange g f F) (c : ℤ) =
      fracExtendCycles (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) := by
  rw [← cancel_mono (HomologicalComplex.iCycles _ _), Category.assoc, Category.assoc,
    HomologicalComplex.cyclesMap_i, Stacks.MapHomologyCycles.mapCycles_i_assoc,
    ← Category.assoc, ← (Scheme.Modules.pullback g).map_comp, fracExtendCycles_comp_iCycles,
    fracExtendCycles_comp_iCycles]
  exact pullback_fracTermTop_comp_extendBaseChange_f g f F

/-- **The class of the fraction commutes with base change, on the Čech complexes**: the
pulled-back class, carried by the comparison `g^*Hᶜ ⟶ Hᶜ g^*` of
`Stacks.MapHomologyCycles.mapHomology` and by the map of Čech complexes, is the class of the
fraction of the pulled-back equations. -/
theorem pullback_classMap_comp_mapHomology_comp_homologyMap :
    (Scheme.Modules.pullback g).map (classMap f F ≫
        ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat
          (Stacks.Perfect.SupportedFraction.embeddingUpNat_f c)).inv) ≫
      Stacks.MapHomologyCycles.mapHomology (Scheme.Modules.pullback g)
        ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ) ≫
      HomologicalComplex.homologyMap (extendBaseChange g f F) (c : ℤ) =
    classMap (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F) ≫
      ((cplx (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)).extendHomologyIso
        ComplexShape.embeddingUpNat (Stacks.Perfect.SupportedFraction.embeddingUpNat_f c)).inv := by
  have : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback g) :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).leftAdjoint_preservesColimits
  rw [← classExtendHomology, ← classExtendHomology, classExtendHomology_eq,
    classExtendHomology_eq,
    (Scheme.Modules.pullback g).map_comp, Category.assoc,
    Stacks.MapHomologyCycles.homologyπ_comp_mapHomology_assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc, ← Category.assoc,
    Category.assoc _ (Stacks.MapHomologyCycles.mapCycles _ _ _),
    pullback_fracExtendCycles_comp_mapCycles_comp_cyclesMap]

/-- The `ℤ`-graded extension of the extended alternating Čech complex of `c` equations has no
terms above degree `c`. -/
theorem isStrictlyLE_cplx_extend :
    CochainComplex.IsStrictlyLE ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  by_cases hn : ∃ n : ℕ, (n : ℤ) = i
  · obtain ⟨n, rfl⟩ := hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
    have : IsEmpty (CechCochains.OrdIndex (I := Fin c) m) :=
      Stacks.Perfect.CechSupportRepresentation.isEmpty_ordIndex_of_le (by omega)
    exact (Stacks.Perfect.CechSupportRepresentation.isZero_pi_of_isEmpty _).of_iso
      ((cplx f F).extendXIso ComplexShape.embeddingUpNat rfl)
  · exact HomologicalComplex.isZero_extend_X _ _ i fun n hn' => hn ⟨n, hn'⟩

/-- The comparison of [Stacks, Tag 06YJ] at a cochain complex, written with the comparison of
derived functors read in the spelling `Qh.obj (quotient (f^* P))`. -/
theorem derivedPullbackComparisonOnComplex_eq {X₀ Y₀ : RingedSpace.{u, u}} (h : X₀ ⟶ Y₀)
    (P : CochainComplex (SheafOfModules.{u} (structureSheafRing Y₀)) ℤ) :
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback h).map
        ((DerivedCategory.quotientCompQhIso _).inv.app P) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison h).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P) ≫
      (DerivedCategory.quotientCompQhIso _).hom.app
        (((modulePullback h).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) =
    Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex h P :=
  (id_middle_formal _ _ _ _ (DerivedCategory.Qh.map_id _)).symm

/-- **`i_*R𝓗_Z(ℱ)` has no cohomology above degree `c`**, for `Z` cut out by `c` global equations
and `ℱ` quasi-coherent: it is represented by the extended alternating Čech complex
(`Stacks.Perfect.SupportedFraction.isIso_cechToSupport`, [Stacks, Tag 0G7M]), which has no terms
above degree `c`. -/
theorem isLE_supportPush_equationsClosedSet [F.IsQuasicoherent] :
    ((supportPush (isClosed_equationsClosedSet f)).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).IsLE (c : ℤ) := by
  have := isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl
  have := isStrictlyLE_cplx_extend f F
  exact (DerivedCategory.TStructure.t (C := Y.Modules)).isLE_of_iso
    (asIso (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)) (c : ℤ)

/-- **The top-degree comparison read on the Čech representative.**  The identification of
`Hᶜ(ℱ^•)` with `ℋᶜ_Z(ℱ)` pulled back, followed by the inverse of the top-degree comparison
`Hᶜ(Lg^*K) ≅ g^*Hᶜ(K)` and by the comparison of [Stacks, Tag 06YJ] at the Čech complex, is the
comparison `g^*Hᶜ(ℱ^•) ⟶ Hᶜ(g^*ℱ^•)`. -/
theorem pullback_cechClass_comp_topDegree_inv [F.IsQuasicoherent]
    (hLE : ((supportPush (isClosed_equationsClosedSet f)).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).IsLE (c : ℤ)) :
    (Scheme.Modules.pullback g).map
        ((derivedQHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv ≫
          (DerivedCategory.homologyFunctor Y.Modules (c : ℤ)).map
            (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)) ≫
      (Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackTopDegreeIsoPullback
          g.toLRSHom.toShHom (supportPushSingle (isClosed_equationsClosedSet f) F) (c : ℤ)
          hLE).inv ≫
      (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              g.toLRSHom.toShHom).map
            (@asIso _ _ _ _ (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)
              (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv ≫
          Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex g.toLRSHom.toShHom
            ((cplx f F).extend ComplexShape.embeddingUpNat)) ≫
      (derivedQHomologyIso (((Scheme.Modules.pullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((cplx f F).extend ComplexShape.embeddingUpNat)) (c : ℤ)).hom =
    Stacks.MapHomologyCycles.mapHomology (Scheme.Modules.pullback g)
      ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ) := by
  have e1 := Stacks.AlgebraicGeometry.TopDegreeBaseChange.representativeClass_comp_eq_mapHomology
    g.toLRSHom.toShHom ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ)
    (isStrictlyLE_cplx_extend f F)
    ((DerivedCategory.quotientCompQhIso _).app _ ≪≫
      @asIso _ _ _ _ (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)
        (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)) hLE
  have := isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl
  refine Eq.trans ?_ e1
  refine congr_comp3_formal _ _ _ _ _ _
    (congrArg (Scheme.Modules.pullback g).map
      (classOfRepresentative_quotientCompQhIso _
        (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl) (hφ := this) _).symm) rfl ?_
  refine Eq.trans ?_ (comparisonOfRepresentative_quotientCompQhIso
    (modulePullback g.toLRSHom.toShHom)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom)
    (fun P => (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      g.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) _
    (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl) (hφ := this) _).symm
  exact congrArg (fun z => (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
      ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback g.toLRSHom.toShHom).map
        (@asIso _ _ _ _ (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)
          (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv ≫ z) ≫
      (derivedQHomologyIso (((Scheme.Modules.pullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((cplx f F).extend ComplexShape.embeddingUpNat)) (c : ℤ)).hom)
    (derivedPullbackComparisonOnComplex_eq g.toLRSHom.toShHom _).symm

/-- **The degree-`c` cohomology of the arrow of [Stacks, Tag 0G78], on the Čech complexes.**  It
is read off the derived diagram of [Stacks, Tag 0G7U]: transported back to the Čech complex of
`ℱ`, it is the comparison of [Stacks, Tag 06YJ], the map of Čech complexes in degree `c`, and the
comparison of [Stacks, Tag 0G7L] for the pulled-back equations. -/
theorem homology_supportedBaseChangeDerived [F.IsQuasicoherent] :
    (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
        (supportedBaseChangeDerived g.toLRSHom.toShHom (equationsClosedSet f)
          (isClosed_equationsClosedSet f)
          (derivedPullbackSingleObj g.toLRSHom.toShHom F)) =
      (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
          ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
              g.toLRSHom.toShHom).map
            (@asIso _ _ _ _ (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)
              (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv ≫
          Stacks.DerivedPullback.Composition.derivedPullbackComparisonOnComplex g.toLRSHom.toShHom
            ((cplx f F).extend ComplexShape.embeddingUpNat)) ≫
        (derivedQHomologyIso (((Scheme.Modules.pullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((cplx f F).extend ComplexShape.embeddingUpNat)) (c : ℤ)).hom ≫
        HomologicalComplex.homologyMap (extendBaseChange g f F) (c : ℤ) ≫
        (derivedQHomologyIso ((cplx (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv ≫
        (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
          (cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
            (isClosed_equationsClosedSet_pullback g f)
            (equationsClosedSet_pullback_subset g f)) := by
  have hq := Stacks.Perfect.SupportedFraction.derivedQHomologyIso_hom_naturality
    (extendBaseChange g f F) (c : ℤ)
  have hq' : (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
      (DerivedCategory.Q.map (extendBaseChange g f F)) =
    (derivedQHomologyIso (((Scheme.Modules.pullback g).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj ((cplx f F).extend ComplexShape.embeddingUpNat)) (c : ℤ)).hom ≫
        HomologicalComplex.homologyMap (extendBaseChange g f F) (c : ℤ) ≫
        (derivedQHomologyIso ((cplx (fun j => g.appTop (f j))
          ((Scheme.Modules.pullback g).obj F)).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv :=
    ((Iso.eq_comp_inv _).mpr hq).trans (Category.assoc _ _ _)
  have hι : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g.toLRSHom.toShHom).map
      (@asIso _ _ _ _ (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl)
        (isIso_cechToSupport f F (isClosed_equationsClosedSet f) le_rfl le_rfl)).inv ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        g.toLRSHom.toShHom).map (cechToSupport f F (isClosed_equationsClosedSet f) le_rfl) =
      𝟙 _ :=
    map_comp_eq_id_formal _ _ _ (Iso.inv_hom_id _)
  exact derived_square_formal (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)) _ _ _ _ _ _ _
    _ _ hι (Stacks.Perfect.CechDerivedBaseChange.derivedBaseChangeSquare_cech g f F) hq'

/-- **The class map of [Stacks, Tag 0G7Q] commutes with base change, for every number of
equations.**  For `g : Y' ⟶ Y`, `f : Fin c → Γ(Y, ⊤)` with any `c`, and `ℱ` quasi-coherent, the
pullback of `c_{f₁,…,f_c} : ℱ ⟶ i_*ℋᶜ_Z(ℱ)`, followed by the degree-`c` arrow of
[Stacks, Tag 0G78] at `Lg^*ℱ ⟶ g^*ℱ` and by the identification of the two spellings of
`Z' = g⁻¹(Z)`, is `c_{f'₁,…,f'_c}` for `f'ⱼ = g^♯(fⱼ)`. -/
theorem classMapToSupport_baseChange [F.IsQuasicoherent]
    (hLE : ((supportPush (isClosed_equationsClosedSet f)).obj
      ((DerivedCategory.singleFunctor Y.Modules 0).obj F)).IsLE (c : ℤ)) :
    (Scheme.Modules.pullback g).map
        (Stacks.Perfect.FractionClass.classMapToSupport f F (isClosed_equationsClosedSet f)
          subset_rfl) ≫
      supportedBaseChangePull g.toLRSHom.toShHom (equationsClosedSet f)
        (isClosed_equationsClosedSet f) (c : ℤ)
        (derivedPullbackSingleObj g.toLRSHom.toShHom F) hLE ≫
      eqToHom (congrArg (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).obj
        (supportPushSingle_congr (equationsClosedSet_pullback g f).symm
          (isClosed_equationsClosedSet_pullback g f)
          (isClosed_equationsClosedSet (fun j => g.appTop (f j)))
          ((Scheme.Modules.pullback g).obj F))) =
      Stacks.Perfect.FractionClass.classMapToSupport (fun j => g.appTop (f j))
        ((Scheme.Modules.pullback g).obj F)
        (isClosed_equationsClosedSet (fun j => g.appTop (f j))) subset_rfl := by
  have hobj := supportPushSingle_congr (equationsClosedSet_pullback g f).symm
    (isClosed_equationsClosedSet_pullback g f)
    (isClosed_equationsClosedSet (fun j => g.appTop (f j))) ((Scheme.Modules.pullback g).obj F)
  have e5 : (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
        (cechToDerivedSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
          (isClosed_equationsClosedSet_pullback g f) (equationsClosedSet_pullback_subset g f)) ≫
      eqToHom (congrArg (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).obj hobj) =
      (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
        (cechToSupport (fun j => g.appTop (f j)) ((Scheme.Modules.pullback g).obj F)
          (isClosed_equationsClosedSet (fun j => g.appTop (f j))) subset_rfl) :=
    (whisker_eq _
        (eqToHom_map (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)) hobj).symm).trans
      (((DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map_comp _ _).symm.trans
        (congrArg (DerivedCategory.homologyFunctor Y'.Modules (c : ℤ)).map
          (Stacks.Perfect.CechDegreeCBaseChange.cechToDerivedSupport_comp_eqToHom _ _ _ _ _ _
            (equationsClosedSet_pullback g f).symm hobj)))
  exact final_chase_formal (Scheme.Modules.pullback g) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (homology_supportedBaseChangeDerived g f F)
    (pullback_cechClass_comp_topDegree_inv g f F hLE)
    (pullback_classMap_comp_mapHomology_comp_homologyMap g f F) e5

end Stacks.Gysin

end
