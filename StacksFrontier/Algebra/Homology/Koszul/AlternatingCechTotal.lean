module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.CategoryTheory.Functor.Currying
public import StacksFrontier.Algebra.Homology.HomBicomplexExt
public import StacksFrontier.Algebra.Homology.Koszul.AlternatingCechColimit
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# Koszul Hom complexes and the alternating Čech total complex

Let `A` be a commutative ring and `f₀, …, f_{r-1}` a finite family of elements of `A`. For a
cochain complex `M` of `A`-modules the filtered colimit, over the exponent, of the Hom complexes
`Hom^•(I^•(f^{e+1}), M^•)` is canonically isomorphic to the total complex of the alternating
Čech complex of the complex of sheaves `M^~`, naturally in `M`.

## Main definitions

* `CochainComplex.homBicomplexMap` and `CochainComplex.homBicomplexFunctor`: the Hom bicomplex
  as a bifunctor, contravariant in the source complex and covariant in the target.
* `Koszul.koszulHomDiagramFunctor` and `Koszul.koszulHomColimitFunctor`: the Koszul Hom diagram
  and its filtered colimit, as functors of the coefficient complex.
* `Koszul.alternatingCechTotalPresheafFunctor`: the total alternating Čech complex of a complex
  of abelian presheaves.
* `Koszul.associatedAbelianPresheafComplexFunctor`: the complex of abelian presheaves underlying
  the complex of associated sheaves.
* `Koszul.alternatingCechTotalFunctor`: the total alternating Čech complex of the complex of
  associated sheaves.

## Main results

* `Koszul.koszulHomColimitIsoAlternatingCechTotal`: the canonical natural isomorphism between
  the two.

## Implementation notes

The nonpositive Koszul complex is extended from chain degree `n` to cochain degree `-n` before
the Hom complex is formed. The total differential on bidegree `(p, q)` is `d₁ + (-1)^p d₂`. The
associated sheaf is Mathlib's tilde sheaf on `Spec A`; the basic opens cover their union, so no
hypothesis that they cover `Spec A` is imposed. Both sides are complexes of abelian groups.

The isomorphism is the composite of four steps. The Hom complex of the extended Koszul complex
is the total complex of its Hom bicomplex: the extended Koszul complex is concentrated in the
degrees `-r, …, 0`, so `CochainComplex.HomBicomplex.totalIsoHomComplexOfSupport` applies with no
hypothesis on the coefficient complex. Taking the total complex commutes with the sequential
colimit, because a diagonal of the total complex is a finite coproduct of evaluations. The
colimit of the Hom bicomplexes is computed row by row, where it is the colimit of the
contragredient Koszul complexes. And that colimit is the alternating Čech complex of `M^~` by
Tag 08D0.

## References

* [Stacks Project, Tag 08D0](https://stacks.math.columbia.edu/tag/08D0)
* [Stacks Project, Tag 08D1](https://stacks.math.columbia.edu/tag/08D1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open CochainComplex CochainComplex.HomComplex
open AlgebraicGeometry
open Stacks.LocalCohomology (associatedAbPresheaf associatedAbPresheafMap)

universe v u

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The map of Hom bicomplexes induced by a morphism of source complexes and a morphism of
target complexes: on the `(p, q)` term it sends `t` to `k_{-p} ≫ t ≫ m_q`. -/
noncomputable def homBicomplexMap {K K' M M' : CochainComplex C ℤ}
    (k : K' ⟶ K) (m : M ⟶ M') : homBicomplex K M ⟶ homBicomplex K' M' :=
  HomologicalComplex₂.homMk
    (fun pq ↦ AddCommGrpCat.ofHom
      { toFun := fun t ↦ k.f (-pq.1) ≫ t ≫ m.f pq.2
        map_zero' :=
          show k.f (-pq.1) ≫ (0 : K.X (-pq.1) ⟶ M.X pq.2) ≫ m.f pq.2 = 0 by simp
        map_add' := fun x y ↦
          (congrArg (fun z ↦ k.f (-pq.1) ≫ z)
            (Preadditive.add_comp _ _ _ x y (m.f pq.2))).trans
            (Preadditive.comp_add _ _ _ _ _ _) })
    (by
      intro p p' q h
      apply AddCommGrpCat.hom_ext
      ext t : 1
      change K'.d (-p') (-p) ≫ k.f (-p) ≫ t ≫ m.f q =
        k.f (-p') ≫ (K.d (-p') (-p) ≫ t) ≫ m.f q
      calc K'.d (-p') (-p) ≫ k.f (-p) ≫ t ≫ m.f q
          = (K'.d (-p') (-p) ≫ k.f (-p)) ≫ (t ≫ m.f q) := (Category.assoc _ _ _).symm
        _ = (k.f (-p') ≫ K.d (-p') (-p)) ≫ (t ≫ m.f q) :=
              congrArg (fun z ↦ z ≫ (t ≫ m.f q)) (k.comm (-p') (-p)).symm
        _ = k.f (-p') ≫ K.d (-p') (-p) ≫ t ≫ m.f q := Category.assoc _ _ _
        _ = k.f (-p') ≫ (K.d (-p') (-p) ≫ t) ≫ m.f q :=
              congrArg (fun z ↦ k.f (-p') ≫ z) (Category.assoc _ _ _).symm)
    (by
      intro p q q' h
      apply AddCommGrpCat.hom_ext
      ext t : 1
      change (k.f (-p) ≫ t ≫ m.f q) ≫ M'.d q q' = k.f (-p) ≫ (t ≫ M.d q q') ≫ m.f q'
      calc (k.f (-p) ≫ t ≫ m.f q) ≫ M'.d q q'
          = k.f (-p) ≫ (t ≫ m.f q) ≫ M'.d q q' := Category.assoc _ _ _
        _ = k.f (-p) ≫ t ≫ m.f q ≫ M'.d q q' :=
              congrArg (fun z ↦ k.f (-p) ≫ z) (Category.assoc _ _ _)
        _ = k.f (-p) ≫ t ≫ M.d q q' ≫ m.f q' :=
              congrArg (fun z ↦ k.f (-p) ≫ t ≫ z) (m.comm q q')
        _ = k.f (-p) ≫ (t ≫ M.d q q') ≫ m.f q' :=
              congrArg (fun z ↦ k.f (-p) ≫ z) (Category.assoc _ _ _).symm)

/-- The `(p, q)` component of `homBicomplexMap` is `t ↦ k_{-p} ≫ t ≫ m_q`. -/
theorem homBicomplexMap_f_f_apply {K K' M M' : CochainComplex C ℤ}
    (k : K' ⟶ K) (m : M ⟶ M') (p q : ℤ) (t : K.X (-p) ⟶ M.X q) :
    ((homBicomplexMap k m).f p).f q t = k.f (-p) ≫ t ≫ m.f q :=
  rfl

/-- The Hom bicomplex as a bifunctor, contravariant in the source complex and covariant in the
target. -/
noncomputable def homBicomplexFunctor (C : Type u) [Category.{v} C] [Abelian C] :
    (CochainComplex C ℤ)ᵒᵖ × CochainComplex C ℤ ⥤
      HomologicalComplex₂ AddCommGrpCat.{v} (up ℤ) (up ℤ) where
  obj X := homBicomplex X.1.unop X.2
  map g := homBicomplexMap g.1.unop g.2
  map_id X := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply AddCommGrpCat.hom_ext
    ext t : 1
    change (𝟙 (X.1.unop.X (-p)) ≫ t ≫ 𝟙 (X.2.X q)) = t
    rw [Category.id_comp]
    exact Category.comp_id t
  map_comp g h := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply HomologicalComplex.Hom.ext
    funext q
    apply AddCommGrpCat.hom_ext
    ext t : 1
    change (h.1.unop.f (-p) ≫ g.1.unop.f (-p)) ≫ t ≫ (g.2.f q ≫ h.2.f q) =
      h.1.unop.f (-p) ≫ (g.1.unop.f (-p) ≫ t ≫ g.2.f q) ≫ h.2.f q
    simp only [Category.assoc]
    exact congrArg (fun z ↦ h.1.unop.f (-p) ≫ g.1.unop.f (-p) ≫ z)
      (Category.assoc t (g.2.f q) (h.2.f q)).symm

end CochainComplex

namespace Koszul

open StacksDraft.DerivedHom.Model (Complex)

variable {A : Type u} [CommRing A]

/-! ### The two functors to be compared -/

/-- The Koszul Hom diagram, functorial in its coefficient complex. -/
noncomputable abbrev koszulHomDiagramFunctor {r : ℕ} (f : Fin r → A) :
    Complex A ⥤ (ℕ ⥤ Complex A) :=
  (((koszulIdealComplexSystem f).diagram ⋙
      embeddingDownNat.extendFunctor (ModuleCat.{u} A)).rightOp ⋙
    Functor.curry.obj (StacksDraft.DerivedHom.Model.homComplexFunctor A)).flip

/-- The filtered colimit `colim_e Hom^•(I^•(f^{e+1}), M^•)`, functorial in `M`. -/
noncomputable abbrev koszulHomColimitFunctor {r : ℕ} (f : Fin r → A) :
    Complex A ⥤ Complex A :=
  koszulHomDiagramFunctor f ⋙ colim

/-- The total alternating Čech complex functor on complexes of abelian presheaves. -/
noncomputable abbrev alternatingCechTotalPresheafFunctor {X : TopCat.{u}} {I : Type v}
    (U : I → Opens X) :
    CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} X) ℤ ⥤
      CochainComplex AddCommGrpCat.{max v u} ℤ :=
  ((Stacks.Cech.alternatingCechComplexFunctor U ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{max v u}).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor AddCommGrpCat.{max v u} (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{max v u} (up ℤ) (up ℤ) (up ℤ)

/-- The underlying complex of abelian presheaves of the complex of associated sheaves. -/
noncomputable abbrev associatedAbelianPresheafComplexFunctor (A : Type u) [CommRing A] :
    Complex A ⥤
      CochainComplex (TopCat.Presheaf AddCommGrpCat.{u} (Spec (CommRingCat.of A))) ℤ := by
  letI : (AlgebraicGeometry.tilde.functor (CommRingCat.of A)).Additive :=
    AlgebraicGeometry.instAdditiveModuleCatCarrierModulesSpecFunctor
  letI : (Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  exact (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).mapHomologicalComplex (up ℤ)

/-- The total alternating Čech complex of the complex of associated sheaves. -/
noncomputable abbrev alternatingCechTotalFunctor {A : Type u} [CommRing A] {r : ℕ}
    (f : Fin r → A) : Complex A ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  associatedAbelianPresheafComplexFunctor A ⋙
    alternatingCechTotalPresheafFunctor
      (X := (Spec (CommRingCat.of A)).toPresheafedSpace)
      (fun i ↦ PrimeSpectrum.basicOpen (f i))

/-! ### The extended Koszul complex has finite support -/

/-- An exterior power of `Aʳ` above the rank vanishes. -/
@[sga "6 VII 4.1" "special case"]
theorem isZero_exteriorPower_fin_of_lt (r n : ℕ) (hn : r < n) :
    IsZero (ModuleCat.of A (⋀[A]^n (Fin r → A))) := by
  classical
  have hEmpty : IsEmpty (Set.powersetCard (Fin r) n) := ⟨fun s ↦ by
    have hcard : s.1.card ≤ r := by simpa using (Finset.card_le_univ s.1)
    have hsize : s.1.card = n := s.prop
    omega⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr ⟨fun _ _ ↦
    (Stacks.RegularSequence.wedgeBasis A r n).repr.injective
      (Finsupp.ext fun i ↦ (hEmpty.false i).elim)⟩

/-- The truncated Koszul complex on the powers of a family of `r` elements vanishes in chain
degrees at least `r`. -/
theorem isZero_koszulIdealComplexPower_of_lt {r : ℕ} (f : Fin r → A) (e n : ℕ)
    (hn : r < n + 1) : IsZero ((koszulIdealComplexPower f e).X n) :=
  isZero_exteriorPower_fin_of_lt r (n + 1) hn

/-- The extension of the truncated Koszul complex to a cochain complex vanishes below `-r`. -/
theorem isZero_koszulExtension_below {r : ℕ} (f : Fin r → A) (e : ℕ) (i : ℤ)
    (hi : i < -(r : ℤ)) :
    IsZero (((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
      (koszulIdealComplexPower f e)).X i) := by
  have hdeg : embeddingDownNat.f (Int.toNat (-i)) = i := by
    show -(Int.toNat (-i) : ℤ) = i
    omega
  have hn : r < Int.toNat (-i) + 1 := by omega
  exact IsZero.of_iso (isZero_koszulIdealComplexPower_of_lt f e (Int.toNat (-i)) hn)
    (HomologicalComplex.extendXIso _ embeddingDownNat hdeg)

/-- The extension of a chain complex along `embeddingDownNat` vanishes in positive degrees. -/
private theorem isZero_extend_down_X_neg (K : ChainComplex (ModuleCat.{u} A) ℕ) (p : ℤ)
    (hp : p < 0) : IsZero ((K.extend embeddingDownNat).X (-p)) := by
  apply HomologicalComplex.isZero_extend_X
  intro j h
  change -(j : ℤ) = -p at h
  omega

/-- Outside `Finset.Icc 0 r` the reflected terms of the extended Koszul complex vanish. -/
theorem koszulExtension_support {r : ℕ} (f : Fin r → A) (e : ℕ) :
    ∀ p ∉ Finset.Icc (0 : ℤ) r,
      IsZero (((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (koszulIdealComplexPower f e)).X (-p)) := by
  intro p hp
  simp only [Finset.mem_Icc, not_and_or, not_le] at hp
  rcases hp with hp | hp
  · exact isZero_extend_down_X_neg _ p hp
  · exact isZero_koszulExtension_below f e (-p) (by omega)

/-- All summands of the Hom bicomplex of the extended Koszul complex outside
`Finset.Icc 0 r` vanish, for every coefficient complex and in every degree. -/
theorem hasVanishingSummands_koszulExtension {r : ℕ} (f : Fin r → A) (e : ℕ)
    (M : Complex A) (n : ℤ) :
    HomBicomplex.HasVanishingSummands
      ((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (koszulIdealComplexPower f e)) M (Finset.Icc (0 : ℤ) r) n :=
  HomBicomplex.hasVanishingSummands_of_isZero_left _ M (koszulExtension_support f e) n

/-- The comparison morphism from the total Hom bicomplex into the complex of abelian groups
underlying the `A`-linear Hom complex. The two targets are the same complex; naming the
`A`-linear one keeps the comparison in the shape the Koszul Hom diagram uses. -/
noncomputable def totalToHomComplexForget (K M : Complex A) :
    (homBicomplex K M).total (up ℤ) ⟶
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj
        (HomComplexR A K M) :=
  HomBicomplex.totalToHomComplex K M

/-- The `(p, q)` summand of the comparison, in the same spelling. -/
noncomputable def summandToForget (K M : Complex A) (p q n : ℤ) :
    ((homBicomplex K M).X p).X q ⟶
      (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj
        (HomComplexR A K M)).X n :=
  HomBicomplex.summandTo K M p q n

/-- On the `(p, q)` summand, `totalToHomComplexForget` restricts to `summandToForget`. -/
theorem ιTotal_totalToHomComplexForget (K M : Complex A) (p q n : ℤ)
    (hpq : (up ℤ).π (up ℤ) (up ℤ) (p, q) = n) :
    (homBicomplex K M).ιTotal (up ℤ) p q n hpq ≫ (totalToHomComplexForget K M).f n =
      summandToForget K M p q n :=
  HomBicomplex.ιTotal_totalToHomComplexX K M p q n hpq

/-- The total complex of the Hom bicomplex of the extended Koszul complex is its Hom
complex. -/
noncomputable def koszulHomTotalIso {r : ℕ} (f : Fin r → A) (e : ℕ) (M : Complex A) :
    (homBicomplex ((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (koszulIdealComplexPower f e)) M).total (up ℤ) ≅
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).obj
        (HomComplexR A ((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
          (koszulIdealComplexPower f e)) M) :=
  HomBicomplex.totalIsoHomComplexOfSupport _ M (Finset.Icc (0 : ℤ) r)
    (hasVanishingSummands_koszulExtension f e M)

/-- The forward map of `koszulHomTotalIso` is `totalToHomComplexForget`. -/
theorem koszulHomTotalIso_hom {r : ℕ} (f : Fin r → A) (e : ℕ) (M : Complex A) :
    (koszulHomTotalIso f e M).hom =
      totalToHomComplexForget ((embeddingDownNat.extendFunctor (ModuleCat.{u} A)).obj
        (koszulIdealComplexPower f e)) M :=
  rfl

/-- The comparison from the total Hom bicomplex to the Hom complex is natural in both
variables: on the bicomplex side the maps are `homBicomplexMap`, and on the Hom complex side
pre- and postcomposition. -/
theorem total_map_homBicomplexMap_comp_totalToHomComplex
    {K K' M M' : Complex A} (k : K' ⟶ K) (m : M ⟶ M') :
    HomologicalComplex₂.total.map (homBicomplexMap k m) (up ℤ) ≫
      totalToHomComplexForget K' M' =
    totalToHomComplexForget K M ≫
      ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)).map
        (Stacks.HomComplex.TensorHomMap.precomp A K' K M k ≫
          Stacks.HomComplex.TensorHomMap.postcomp A K' M M' m) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  simp only [HomologicalComplex.comp_f]
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc,
    ιTotal_totalToHomComplexForget, ← Category.assoc, ιTotal_totalToHomComplexForget]
  apply AddCommGrpCat.hom_ext
  ext t : 1
  change (K.X (-p) ⟶ M.X q) at t
  show HomBicomplex.sign p q • Cochain.single (k.f (-p) ≫ t ≫ m.f q) n =
    ((Cochain.ofHom k).comp (HomBicomplex.sign p q • Cochain.single t n) (zero_add n)).comp
      (Cochain.ofHom m) (add_zero n)
  rw [Cochain.comp_units_smul, Cochain.units_smul_comp]
  congr 1
  apply Cochain.ext
  intro a b hab
  simp only [Cochain.comp_zero_cochain_v, Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  by_cases ha : a = -p
  · subst a
    have hb : b = q := by
      simp only [ComplexShape.π_def] at hpq
      omega
    cases hb
    simp only [Cochain.single_v]
    exact (Category.assoc _ _ _).symm
  · simp only [Cochain.single_v_eq_zero _ _ _ _ _ ha, zero_comp, comp_zero]

/-! ### The Hom bicomplex diagram and its total complex -/

/-- The diagram of Hom bicomplexes of the extended truncated Koszul complexes. -/
noncomputable abbrev koszulHomBicomplexDiagramFunctor {r : ℕ} (f : Fin r → A) :
    Complex A ⥤ (ℕ ⥤ HomologicalComplex₂ AddCommGrpCat.{u} (up ℤ) (up ℤ)) :=
  (((koszulIdealComplexSystem f).diagram ⋙
      embeddingDownNat.extendFunctor (ModuleCat.{u} A)).rightOp ⋙
    Functor.curry.obj (homBicomplexFunctor (ModuleCat.{u} A))).flip

/-- Degreewise, the total complex of the Hom bicomplex of a stage is the Hom complex of that
stage. -/
noncomputable def koszulHomTotalDiagramIso {r : ℕ} (f : Fin r → A) (M : Complex A) :
    (koszulHomBicomplexDiagramFunctor f).obj M ⋙
        HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ) ≅
      (koszulHomDiagramFunctor f).obj M ⋙
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) := by
  refine NatIso.ofComponents (fun e ↦ koszulHomTotalIso f e M) ?_
  intro e e' g
  exact total_map_homBicomplexMap_comp_totalToHomComplex _ (𝟙 M)

/-- The degreewise identification of the previous result is natural in the coefficient
complex. -/
noncomputable def koszulHomTotalDiagramNatIso {r : ℕ} (f : Fin r → A) :
    koszulHomBicomplexDiagramFunctor f ⋙
        (Functor.whiskeringRight ℕ _ _).obj
          (HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)) ≅
      koszulHomDiagramFunctor f ⋙
        (Functor.whiskeringRight ℕ _ _).obj
          ((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)) := by
  refine NatIso.ofComponents (koszulHomTotalDiagramIso f) ?_
  intro M N g
  apply NatTrans.ext
  funext e
  exact total_map_homBicomplexMap_comp_totalToHomComplex (𝟙 _) g

/-- The Hom-total comparison commutes with the filtered Koszul power system. -/
noncomputable def koszulHomColimitIsoBicomplexTotal {r : ℕ} (f : Fin r → A) :
    koszulHomColimitFunctor f ⋙
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) ≅
      (koszulHomBicomplexDiagramFunctor f ⋙ colim) ⋙
        HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ) := by
  let T := HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)
  let F := (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)
  letI : PreservesColimitsOfShape ℕ T :=
    ⟨fun {D} ↦ CochainComplex.KFlat.preservesColimit_totalFunctor (up ℤ) D⟩
  exact Functor.isoWhiskerLeft (koszulHomDiagramFunctor f) (preservesColimitNatIso F) ≪≫
    Functor.isoWhiskerRight (koszulHomTotalDiagramNatIso f).symm colim ≪≫
    Functor.isoWhiskerLeft (koszulHomBicomplexDiagramFunctor f) (preservesColimitNatIso T).symm

/-! ### The rows of the Hom bicomplex diagram -/

/-- The cochain complex `p ↦ Hom(K⁻ᵖ, M)` of a single coefficient module. -/
noncomputable def homModuleComplex (K : Complex A) (M : ModuleCat.{u} A) :
    CochainComplex AddCommGrpCat.{u} ℤ where
  X p := AddCommGrpCat.of (K.X (-p) ⟶ M)
  d p p' := AddCommGrpCat.ofHom
    { toFun := fun t ↦ K.d (-p') (-p) ≫ t
      map_zero' := by simp
      map_add' _ _ := by simp }
  shape p p' h := by
    apply AddCommGrpCat.hom_ext
    ext t : 1
    change K.d (-p') (-p) ≫ t = 0
    rw [K.shape _ _ (by simp only [up_Rel] at *; omega), zero_comp]
  d_comp_d' p p' p'' _ _ := by
    apply AddCommGrpCat.hom_ext
    ext t : 1
    change K.d (-p'') (-p') ≫ K.d (-p') (-p) ≫ t = 0
    rw [← Category.assoc, K.d_comp_d, zero_comp]

/-- In nonnegative degrees the complex `Hom(K⁻ᵖ, M)` of the extended Koszul complex is the
contragredient Koszul complex. -/
noncomputable def homModuleExtensionXIso (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (M : ModuleCat.{u} A) (p : ℕ) :
    (homModuleComplex (K.extend embeddingDownNat) M).X p ≅ (koszulHomComplex K M).X p where
  hom := AddCommGrpCat.ofHom
    (ModuleCat.homAddEquiv.toAddMonoidHom.comp
      (Preadditive.leftComp M (K.extendXIso embeddingDownNat (i := p) rfl).inv))
  inv := AddCommGrpCat.ofHom
    ((Preadditive.leftComp M (K.extendXIso embeddingDownNat (i := p) rfl).hom).comp
      ModuleCat.homAddEquiv.symm.toAddMonoidHom)
  hom_inv_id := by
    apply AddCommGrpCat.hom_ext
    ext t : 1
    exact (K.extendXIso embeddingDownNat (i := p) rfl).hom_inv_id_assoc t
  inv_hom_id := by
    apply AddCommGrpCat.hom_ext
    ext t : 1
    exact (congrArg ModuleCat.homAddEquiv
      ((K.extendXIso embeddingDownNat (i := p) rfl).inv_hom_id_assoc
        (ModuleCat.homAddEquiv.symm t))).trans (ModuleCat.homAddEquiv.apply_symm_apply t)

/-- The restriction to nonnegative degrees of `Hom((K extended)⁻ᵖ, M)` is the contragredient
Koszul complex. -/
noncomputable def homModuleRestrictionIso (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (M : ModuleCat.{u} A) :
    (homModuleComplex (K.extend embeddingDownNat) M).restriction embeddingUpNat ≅
      koszulHomComplex K M := by
  refine HomologicalComplex.Hom.isoOfComponents (homModuleExtensionXIso K M) ?_
  intro p p' h
  obtain rfl : p + 1 = p' := h
  apply AddCommGrpCat.hom_ext
  ext t : 1
  change ((K.extend embeddingDownNat).X (embeddingDownNat.f p) ⟶ M) at t
  rw [koszulHomComplex_d]
  change (ModuleCat.Hom.hom ((K.extendXIso embeddingDownNat (i := p) rfl).inv ≫ t)).comp
      (K.d (p + 1) p).hom =
    ((K.extendXIso embeddingDownNat (i := p + 1) rfl).inv ≫
      (K.extend embeddingDownNat).d (embeddingDownNat.f (p + 1)) (embeddingDownNat.f p) ≫
        t).hom
  rw [K.extend_d_eq embeddingDownNat (i := p + 1) (j := p) rfl rfl]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  rfl

/-- In negative degrees `Hom((K extended)⁻ᵖ, M)` vanishes. -/
theorem homModuleExtension_isZero (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (M : ModuleCat.{u} A) (p : ℤ) (hp : p < 0) :
    IsZero ((homModuleComplex (K.extend embeddingDownNat) M).X p) := by
  have : Subsingleton ((homModuleComplex (K.extend embeddingDownNat) M).X p) :=
    ⟨fun t t' ↦ (isZero_extend_down_X_neg K p hp).eq_of_src t t'⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

/-- `Hom((K extended)⁻ᵖ, M)` is the extension of the contragredient Koszul complex. -/
noncomputable def homModuleExtensionIso (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (M : ModuleCat.{u} A) :
    homModuleComplex (K.extend embeddingDownNat) M ≅
      (koszulHomComplex K M).extend embeddingUpNat := by
  let φ := (homModuleRestrictionIso K M).hom
  have hφ : embeddingUpNat.HasLift φ := by
    intro j hj i hi
    have hn : i < 0 := by
      by_contra hn
      exact hj.notMem hi i.toNat (Int.toNat_of_nonneg (by omega))
    exact (homModuleExtension_isZero K M i hn).eq_of_src _ _
  let ψ := embeddingUpNat.liftExtend φ hφ
  have (p : ℤ) : IsIso (ψ.f p) := by
    by_cases hp : p < 0
    · exact (homModuleExtension_isZero K M p hp).isIso
        ((koszulHomComplex K M).isZero_extend_X embeddingUpNat p (by
          intro i h
          change (i : ℤ) = p at h
          omega)) _
    · have h : embeddingUpNat.f p.toNat = p := Int.toNat_of_nonneg (by omega)
      exact (embeddingUpNat.isIso_liftExtend_f_iff φ hφ h).mpr inferInstance
  haveI : IsIso ψ := HomologicalComplex.Hom.isIso_of_components ψ
  exact asIso ψ

/-- Functoriality of `Hom(K⁻ᵖ, M)` in the source complex and the coefficient module. -/
noncomputable def homModuleMap {K K' : Complex A} {M M' : ModuleCat.{u} A}
    (k : K' ⟶ K) (m : M ⟶ M') : homModuleComplex K M ⟶ homModuleComplex K' M' where
  f p := AddCommGrpCat.ofHom
    { toFun := fun t ↦ k.f (-p) ≫ t ≫ m
      map_zero' := by simp
      map_add' _ _ := by simp }
  comm' p p' _ := by
    apply AddCommGrpCat.hom_ext
    ext t : 1
    change K'.d (-p') (-p) ≫ (k.f (-p) ≫ t ≫ m) =
      k.f (-p') ≫ (K.d (-p') (-p) ≫ t) ≫ m
    calc K'.d (-p') (-p) ≫ (k.f (-p) ≫ t ≫ m)
        = (K'.d (-p') (-p) ≫ k.f (-p)) ≫ (t ≫ m) := (Category.assoc _ _ _).symm
      _ = (k.f (-p') ≫ K.d (-p') (-p)) ≫ (t ≫ m) :=
            congrArg (fun z ↦ z ≫ (t ≫ m)) (k.comm (-p') (-p)).symm
      _ = k.f (-p') ≫ K.d (-p') (-p) ≫ t ≫ m := Category.assoc _ _ _
      _ = k.f (-p') ≫ (K.d (-p') (-p) ≫ t) ≫ m :=
            congrArg (fun z ↦ k.f (-p') ≫ z) (Category.assoc _ _ _).symm

/-- The identification with the extension of the contragredient Koszul complex is natural. -/
theorem homModuleExtensionIso_naturality
    {K K' : ChainComplex (ModuleCat.{u} A) ℕ} {M M' : ModuleCat.{u} A}
    (k : K' ⟶ K) (m : M ⟶ M') :
    homModuleMap (HomologicalComplex.extendMap k embeddingDownNat) m ≫
      (homModuleExtensionIso K' M').hom =
    (homModuleExtensionIso K M).hom ≫
      HomologicalComplex.extendMap
        (koszulHomComplexPrecomp k M ≫ koszulHomComplexMap K' m) embeddingUpNat := by
  apply (embeddingUpNat.homEquiv _ _).injective
  apply Subtype.ext
  show embeddingUpNat.homRestrict (_ ≫ _) = embeddingUpNat.homRestrict (_ ≫ _)
  have h (L : ChainComplex (ModuleCat.{u} A) ℕ) (N : ModuleCat.{u} A) :
      embeddingUpNat.homRestrict (homModuleExtensionIso L N).hom =
        (homModuleRestrictionIso L N).hom := by
    simp only [homModuleExtensionIso, asIso_hom]
    exact ComplexShape.Embedding.homRestrict_liftExtend _ _ _
  rw [ComplexShape.Embedding.homRestrict_comp_extendMap,
    ComplexShape.Embedding.homRestrict_precomp, h, h]
  apply HomologicalComplex.hom_ext
  intro p
  apply AddCommGrpCat.hom_ext
  ext t : 1
  have hp : embeddingDownNat.f p = -(p : ℤ) := rfl
  change (K.extend embeddingDownNat).X (-(p : ℤ)) ⟶ M at t
  show ((K'.extendXIso embeddingDownNat (i := p) hp).inv ≫
      (HomologicalComplex.extendMap k embeddingDownNat).f (-(p : ℤ)) ≫ t ≫ m).hom =
    m.hom.comp
      (((K.extendXIso embeddingDownNat (i := p) hp).inv ≫ t).hom.comp (k.f p).hom)
  rw [HomologicalComplex.extendMap_f k embeddingDownNat (i := p) (i' := -(p : ℤ)) hp]
  simp only [Iso.inv_hom_id_assoc, Category.assoc]
  rfl

/-! ### Each row is the colimit of the contragredient Koszul complexes -/

/-- The identification of the `e`-th row with the extended contragredient complex, written in
the spelling the Koszul Hom diagram uses. -/
noncomputable def homModuleExtensionDiagramIso {r : ℕ} (f : Fin r → A) (e : ℕ)
    (N : ModuleCat.{u} A) :
    homModuleComplex
        (((koszulIdealComplexSystem f).diagram.obj (op e)).extend embeddingDownNat) N ≅
      ((koszulHomDiagram f N).obj e).extend embeddingUpNat :=
  homModuleExtensionIso (koszulIdealComplexPower f e) N

/-- Compatibility of that identification with the transitions of the two systems. -/
theorem homModuleExtensionDiagramIso_transition {r : ℕ} (f : Fin r → A) (e : ℕ)
    (N : ModuleCat.{u} A) :
    homModuleMap (HomologicalComplex.extendMap
        ((koszulIdealComplexSystem f).diagram.map (homOfLE (Nat.le_add_right e 1)).op)
        embeddingDownNat) (𝟙 N) ≫ (homModuleExtensionDiagramIso f (e + 1) N).hom =
      (homModuleExtensionDiagramIso f e N).hom ≫
        HomologicalComplex.extendMap
          ((koszulHomDiagram f N).map (homOfLE (Nat.le_add_right e 1))) embeddingUpNat := by
  rw [show (koszulIdealComplexSystem f).diagram.map (homOfLE (Nat.le_add_right e 1)).op =
      (koszulIdealComplexSystem f).transition e from
      Functor.ofOpSequence_map_homOfLE_succ _ e,
    koszulHomDiagram_map_succ]
  have hnat := homModuleExtensionIso_naturality
    ((koszulIdealComplexSystem f).transition e) (𝟙 N)
  simp only [koszulHomComplexMap_id, Category.comp_id] at hnat
  exact hnat

/-- Naturality of that identification in the coefficient module, in the same spelling. -/
theorem homModuleExtensionDiagramIso_naturality {r : ℕ} (f : Fin r → A) (e : ℕ)
    {N N' : ModuleCat.{u} A} (m : N ⟶ N') :
    homModuleMap
        (𝟙 (((koszulIdealComplexSystem f).diagram.obj (op e)).extend embeddingDownNat)) m ≫
        (homModuleExtensionDiagramIso f e N').hom =
      (homModuleExtensionDiagramIso f e N).hom ≫
        HomologicalComplex.extendMap ((koszulHomDiagramMap f m).app e) embeddingUpNat := by
  have h := homModuleExtensionIso_naturality (𝟙 (koszulIdealComplexPower f e)) m
  simp only [koszulHomComplexPrecomp_id, Category.id_comp,
    HomologicalComplex.extendMap_id] at h
  exact h


/-- The functor sending a module to the colimit of the contragredient Koszul complexes. -/
noncomputable def moduleKoszulHomColimitFunctor {r : ℕ} (f : Fin r → A) :
    ModuleCat.{u} A ⥤ CochainComplex AddCommGrpCat.{u} ℕ where
  obj M := colimit (koszulHomDiagram f M)
  map g := colim.map (koszulHomDiagramMap f g)
  map_id M := by
    change colim.map (koszulHomDiagramMap f (𝟙 M)) = 𝟙 _
    rw [show koszulHomDiagramMap f (𝟙 M) = 𝟙 _ by ext e p t; rfl]
    exact colim.map_id _
  map_comp g h := by
    change colim.map (koszulHomDiagramMap f (g ≫ h)) =
      colim.map (koszulHomDiagramMap f g) ≫ colim.map (koszulHomDiagramMap f h)
    rw [show koszulHomDiagramMap f (g ≫ h) =
      koszulHomDiagramMap f g ≫ koszulHomDiagramMap f h by ext e p t; rfl]
    exact colim.map_comp _ _

/-- The functor sending a module to the alternating Čech complex of its associated sheaf. -/
noncomputable def moduleAlternatingCechFunctor {r : ℕ} (f : Fin r → A) :
    ModuleCat.{u} A ⥤ CochainComplex AddCommGrpCat.{u} ℕ where
  obj M := moduleAlternatingCechComplex f M
  map g := moduleAlternatingCechMap f g
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    ext x
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext y
    change IsLocalizedModule.map y.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M) LinearMap.id
        ((x.1 i).1 y) = (x.1 i).1 y
    rw [IsLocalizedModule.map_id]
    rfl
  map_comp {M N P} (g : M ⟶ N) (h : N ⟶ P) := by
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    ext x
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext y
    change IsLocalizedModule.map y.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P)
        (ModuleCat.Hom.hom h ∘ₗ ModuleCat.Hom.hom g) ((x.1 i).1 y) =
      IsLocalizedModule.map y.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P) (ModuleCat.Hom.hom h)
        (IsLocalizedModule.map y.1.asIdeal.primeCompl
          (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
          (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) (ModuleCat.Hom.hom g)
          ((x.1 i).1 y))
    rw [IsLocalizedModule.map_comp' y.1.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N)
      (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl P)
      (ModuleCat.Hom.hom g) (ModuleCat.Hom.hom h)]
    rfl

/-- Tag 08D0, as a natural isomorphism of functors of the coefficient module. -/
noncomputable def moduleAlternatingCechNatIso {r : ℕ} (f : Fin r → A) :
    moduleKoszulHomColimitFunctor f ≅ moduleAlternatingCechFunctor f :=
  NatIso.ofComponents (alternatingCechComplexIso f)
    (fun {M N} g ↦ (alternatingCechComplexIso_naturality f M N g).symm)

/-- The alternating Čech complex functor of the coefficient module preserves zero morphisms. -/
instance moduleAlternatingCechFunctor_preservesZeroMorphisms {r : ℕ} (f : Fin r → A) :
    (moduleAlternatingCechFunctor f).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    apply HomologicalComplex.Hom.ext
    funext p
    apply AddCommGrpCat.hom_ext
    ext x
    apply Subtype.ext
    funext i
    apply Subtype.ext
    funext y
    change IsLocalizedModule.map y.1.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl M)
        (LocalizedModule.mkLinearMap y.1.asIdeal.primeCompl N) 0 ((x.1 i).1 y) = 0
    simp

/-- The colimit of the Koszul Hom complexes, as a functor of the coefficient module, preserves
zero morphisms. -/
instance moduleKoszulHomColimitFunctor_preservesZeroMorphisms {r : ℕ} (f : Fin r → A) :
    (moduleKoszulHomColimitFunctor f).PreservesZeroMorphisms where
  map_zero := by
    intro M N
    change colim.map (koszulHomDiagramMap f (0 : M ⟶ N)) = 0
    rw [show koszulHomDiagramMap f (0 : M ⟶ N) = 0 by ext e p t; rfl]
    exact Functor.map_zero
      (colim (J := ℕ) (C := CochainComplex AddCommGrpCat.{u} ℕ)) _ _

/-- The total alternating Čech complex, built from the module-level Čech functor. -/
noncomputable def moduleCechTotalFunctor {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  ((moduleAlternatingCechFunctor f ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)

/-- The total complex built from the module-level colimit of contragredient Koszul
complexes. -/
noncomputable def moduleKoszulHomTotalFunctor {r : ℕ} (f : Fin r → A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex AddCommGrpCat.{u} ℤ :=
  ((moduleKoszulHomColimitFunctor f ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ)) ⋙
    HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ)

/-- Tag 08D0, propagated to the two total complexes. -/
noncomputable def moduleKoszulHomTotalIso {r : ℕ} (f : Fin r → A) :
    moduleKoszulHomTotalFunctor f ≅ moduleCechTotalFunctor f := by
  let e : moduleKoszulHomColimitFunctor f ⋙
      embeddingUpNat.extendFunctor AddCommGrpCat.{u} ≅
      moduleAlternatingCechFunctor f ⋙
        embeddingUpNat.extendFunctor AddCommGrpCat.{u} :=
    Functor.isoWhiskerRight (moduleAlternatingCechNatIso f)
      (embeddingUpNat.extendFunctor AddCommGrpCat.{u})
  exact Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (up ℤ))
    (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ))

/-! ### Comparison with Mathlib's tilde -/

/-- On modules in the ring's own universe the locally fractional presheaf map is the tilde of
the module map. -/
theorem associatedAbPresheafMap_eq_tilde {M N : ModuleCat.{u} A} (g : M ⟶ N) :
    associatedAbPresheafMap g =
      (Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).map
        ((AlgebraicGeometry.tilde.functor (CommRingCat.of A)).map g) := by
  ext U s
  rfl

/-- The locally fractional presheaf as a functor of the module. -/
noncomputable def associatedAbPresheafFunctor (A : Type u) [CommRing A] :
    ModuleCat.{u} A ⥤ TopCat.Presheaf AddCommGrpCat.{u} (Spec (CommRingCat.of A)) where
  obj M := associatedAbPresheaf M
  map g := associatedAbPresheafMap g
  map_id M := by
    rw [associatedAbPresheafMap_eq_tilde (𝟙 M)]
    change (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).map (𝟙 M) = _
    exact (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).map_id M
  map_comp g h := by
    rw [associatedAbPresheafMap_eq_tilde (g ≫ h),
      associatedAbPresheafMap_eq_tilde g, associatedAbPresheafMap_eq_tilde h]
    change (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).map (g ≫ h) = _
    exact (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).map_comp g h

/-- The locally fractional presheaf functor is Mathlib's tilde. -/
noncomputable def associatedAbPresheafNatIso (A : Type u) [CommRing A] :
    associatedAbPresheafFunctor A ≅
      (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
        Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))) := by
  refine NatIso.ofComponents (fun M ↦ Iso.refl _) ?_
  intro M N g
  change associatedAbPresheafMap g ≫ _ = _ ≫
    (AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
      Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))).map g
  rw [associatedAbPresheafMap_eq_tilde g]
  rfl

/-- The alternating Čech complex of the associated presheaf, as a functor of the module,
factored through the category of abelian presheaves. -/
noncomputable def moduleCechViaPresheafFunctor {r : ℕ} (f : Fin r → A) :
    ModuleCat.{u} A ⥤ CochainComplex AddCommGrpCat.{u} ℕ :=
  associatedAbPresheafFunctor A ⋙
    Stacks.Cech.alternatingCechComplexFunctor
      (X := (Spec (CommRingCat.of A)).toPresheafedSpace)
      (fun i ↦ PrimeSpectrum.basicOpen (f i))

/-- The two descriptions of the alternating Čech complex of the associated sheaf agree. -/
noncomputable def moduleAlternatingCechViaPresheafIso {r : ℕ} (f : Fin r → A) :
    moduleAlternatingCechFunctor f ≅ moduleCechViaPresheafFunctor f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- The alternating Čech complex of the associated presheaf, as a functor of the module,
preserves zero morphisms. -/
instance moduleCechViaPresheafFunctor_preservesZeroMorphisms {r : ℕ} (f : Fin r → A) :
    (moduleCechViaPresheafFunctor f).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (moduleAlternatingCechViaPresheafIso f)

/-- The module-level total alternating Čech complex is the presheaf-level one applied to the
complex of associated sheaves. -/
noncomputable def moduleCechTotalIsoAlternatingCechTotal {r : ℕ} (f : Fin r → A) :
    moduleCechTotalFunctor f ≅ alternatingCechTotalFunctor f := by
  let U := fun i ↦ PrimeSpectrum.basicOpen (f i)
  let F := Stacks.Cech.alternatingCechComplexFunctor
    (X := (Spec (CommRingCat.of A)).toPresheafedSpace) U
  let G := embeddingUpNat.extendFunctor AddCommGrpCat.{u}
  let α := moduleAlternatingCechViaPresheafIso f ≪≫
    Functor.isoWhiskerRight (associatedAbPresheafNatIso A) F
  let β := Functor.isoWhiskerRight α G
  let H := ((AlgebraicGeometry.tilde.functor (CommRingCat.of A) ⋙
    Scheme.Modules.toPresheaf (Spec (CommRingCat.of A))) ⋙ F) ⋙ G
  letI : H.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_iso β
  let γ := NatIso.mapHomologicalComplex β (up ℤ)
  exact Functor.isoWhiskerRight γ
    (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) ⋙
      HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ))

/-! ### The colimit of the Hom bicomplexes, computed row by row -/

/-- The `q`-th row of the diagram of Hom bicomplexes is the direct system of contragredient
Koszul complexes of `M^q`, extended to `ℤ`. -/
noncomputable def koszulHomRowDiagramIso {r : ℕ} (f : Fin r → A) (M : Complex A) (q : ℤ) :
    (koszulHomBicomplexDiagramFunctor f).obj M ⋙
        HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) ⋙
        HomologicalComplex.eval (CochainComplex AddCommGrpCat.{u} ℤ) (up ℤ) q ≅
      koszulHomDiagram f (M.X q) ⋙ embeddingUpNat.extendFunctor AddCommGrpCat.{u} := by
  let α := NatTrans.ofSequence
    (F := (koszulHomBicomplexDiagramFunctor f).obj M ⋙
      HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) ⋙
      HomologicalComplex.eval (CochainComplex AddCommGrpCat.{u} ℤ) (up ℤ) q)
    (G := koszulHomDiagram f (M.X q) ⋙ embeddingUpNat.extendFunctor AddCommGrpCat.{u})
    (fun e ↦ (homModuleExtensionDiagramIso f e (M.X q)).hom)
    (fun e ↦ homModuleExtensionDiagramIso_transition f e (M.X q))
  haveI : IsIso α := (NatTrans.isIso_iff_isIso_app α).mpr (fun e ↦ by
    change IsIso (homModuleExtensionIso _ _).hom
    infer_instance)
  exact asIso α

/-- The bicomplex of the degreewise colimits of contragredient Koszul complexes. -/
noncomputable abbrev moduleKoszulHomBicomplexFunctor {r : ℕ} (f : Fin r → A) :=
  (moduleKoszulHomColimitFunctor f ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ)

/-- The leg at stage `e` of the cocone exhibiting the bicomplex of degreewise colimits. -/
noncomputable def koszulHomBicomplexCoconeLeg {r : ℕ} (f : Fin r → A)
    (M : Complex A) (e : ℕ) :
    (((koszulHomBicomplexDiagramFunctor f).obj M).obj e).flip ⟶
      (moduleKoszulHomBicomplexFunctor f).obj M where
  f q := (homModuleExtensionDiagramIso f e (M.X q)).hom ≫
    HomologicalComplex.extendMap (colimit.ι (koszulHomDiagram f (M.X q)) e) embeddingUpNat
  comm' q q' _ := by
    change (_ ≫ _) ≫ HomologicalComplex.extendMap
        (colim.map (koszulHomDiagramMap f (M.d q q'))) embeddingUpNat =
      homModuleMap (𝟙 _) (M.d q q') ≫ (_ ≫ _)
    rw [Category.assoc, ← HomologicalComplex.extendMap_comp, colim_map, ι_colimMap,
      HomologicalComplex.extendMap_comp, ← Category.assoc,
      ← homModuleExtensionDiagramIso_naturality, Category.assoc]

/-- The cocone exhibiting the bicomplex of degreewise colimits as the colimit of the diagram
of Hom bicomplexes. -/
noncomputable def koszulHomBicomplexCocone {r : ℕ} (f : Fin r → A) (M : Complex A) :
    Cocone ((koszulHomBicomplexDiagramFunctor f).obj M ⋙
      HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ)) where
  pt := (moduleKoszulHomBicomplexFunctor f).obj M
  ι := NatTrans.ofSequence (koszulHomBicomplexCoconeLeg f M) (fun e ↦ by
    change _ ≫ _ = koszulHomBicomplexCoconeLeg f M e ≫ 𝟙 _
    rw [Category.comp_id]
    apply HomologicalComplex.hom_ext
    intro q
    change homModuleMap (HomologicalComplex.extendMap
        ((koszulIdealComplexSystem f).diagram.map (homOfLE (Nat.le_add_right e 1)).op)
        embeddingDownNat) (𝟙 (M.X q)) ≫
        ((homModuleExtensionDiagramIso f (e + 1) (M.X q)).hom ≫
          HomologicalComplex.extendMap
            (colimit.ι (koszulHomDiagram f (M.X q)) (e + 1)) embeddingUpNat) =
      (homModuleExtensionDiagramIso f e (M.X q)).hom ≫
        HomologicalComplex.extendMap
          (colimit.ι (koszulHomDiagram f (M.X q)) e) embeddingUpNat
    rw [← Category.assoc, homModuleExtensionDiagramIso_transition, Category.assoc,
      ← HomologicalComplex.extendMap_comp, colimit.w])

/-- That cocone is a colimit: the colimit of the Hom bicomplexes is computed row by row. -/
noncomputable def koszulHomBicomplexCoconeIsColimit {r : ℕ} (f : Fin r → A) (M : Complex A) :
    IsColimit (koszulHomBicomplexCocone f M) := by
  apply HomologicalComplex.isColimitOfEval
  intro q
  let E := embeddingUpNat.extendFunctor AddCommGrpCat.{u}
  let D := koszulHomDiagram f (M.X q)
  exact (IsColimit.precomposeHomEquiv (koszulHomRowDiagramIso f M q)
    (E.mapCocone (colimit.cocone D))).symm (isColimitOfPreserves E (colimit.isColimit D))

/-- The legs of that cocone are natural in the coefficient complex. -/
theorem koszulHomBicomplexCoconeLeg_naturality {r : ℕ} (f : Fin r → A)
    {M N : Complex A} (g : M ⟶ N) (e : ℕ) :
    (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ)).map
        (((koszulHomBicomplexDiagramFunctor f).map g).app e) ≫
      koszulHomBicomplexCoconeLeg f N e =
    koszulHomBicomplexCoconeLeg f M e ≫ (moduleKoszulHomBicomplexFunctor f).map g := by
  apply HomologicalComplex.hom_ext
  intro q
  show homModuleMap
      (𝟙 (((koszulIdealComplexSystem f).diagram.obj (op e)).extend embeddingDownNat))
        (g.f q) ≫ (_ ≫ _) =
    (_ ≫ _) ≫ HomologicalComplex.extendMap
      (colim.map (koszulHomDiagramMap f (g.f q))) embeddingUpNat
  symm
  rw [Category.assoc, ← HomologicalComplex.extendMap_comp, colim_map, ι_colimMap,
    HomologicalComplex.extendMap_comp, ← Category.assoc,
    ← homModuleExtensionDiagramIso_naturality, Category.assoc]

-- The comparison of the two spellings `colimit.ι F e ≫ (colimit.isoColimitCocone t).hom` and
-- `t.cocone.ι.app e` is not reached at the default transparency here, because the colimit
-- cocone of the whiskered diagram and the cocone built below are the same cocone only after
-- unfolding `getColimitCocone`, which the module system does not expose.
set_option backward.isDefEq.respectTransparency false in
/-- The colimit of the flipped Hom bicomplexes is the bicomplex of degreewise colimits. -/
noncomputable def koszulHomFlippedColimitIso {r : ℕ} (f : Fin r → A) :
    (koszulHomBicomplexDiagramFunctor f ⋙
      (Functor.whiskeringRight ℕ _ _).obj
        (HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ))) ⋙ colim ≅
      moduleKoszulHomBicomplexFunctor f := by
  refine NatIso.ofComponents (fun M ↦ colimit.isoColimitCocone
    ⟨koszulHomBicomplexCocone f M, koszulHomBicomplexCoconeIsColimit f M⟩) ?_
  intro M N g
  apply colimit.hom_ext
  intro e
  simp only [Functor.comp_map, colim_map, ι_colimMap_assoc,
    colimit.isoColimitCocone_ι_hom, colimit.isoColimitCocone_ι_hom_assoc]
  exact koszulHomBicomplexCoconeLeg_naturality f g e

/-- The total complex of the colimit of the Hom bicomplexes is the module-level total
complex. -/
noncomputable def koszulHomColimitIsoModuleTotal {r : ℕ} (f : Fin r → A) :
    (koszulHomBicomplexDiagramFunctor f ⋙ colim) ⋙
        HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ) ≅
      moduleKoszulHomTotalFunctor f := by
  let S := HomologicalComplex₂.flipFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ)
  letI : S.IsEquivalence :=
    (HomologicalComplex₂.flipEquivalence AddCommGrpCat.{u} (up ℤ) (up ℤ)).isEquivalence_functor
  let α : (koszulHomBicomplexDiagramFunctor f ⋙ colim) ⋙ S ≅
      moduleKoszulHomBicomplexFunctor f :=
    Functor.isoWhiskerLeft (koszulHomBicomplexDiagramFunctor f) (preservesColimitNatIso S) ≪≫
      koszulHomFlippedColimitIso f
  exact Functor.isoWhiskerRight (Functor.isoWhiskerRight α S)
    (HomologicalComplex₂.totalFunctor AddCommGrpCat.{u} (up ℤ) (up ℤ) (up ℤ))

/-- **Stacks Project, Tag 08D1.** The filtered colimit of the Hom complexes from the powers
of the truncated Koszul complex is canonically isomorphic to the total alternating Čech complex
of the associated sheaf complex, naturally in the coefficient complex. -/
@[stacks 08D1]
noncomputable def koszulHomColimitIsoAlternatingCechTotal
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    koszulHomColimitFunctor f ⋙
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex (up ℤ) ≅
      alternatingCechTotalFunctor f :=
  koszulHomColimitIsoBicomplexTotal f ≪≫ koszulHomColimitIsoModuleTotal f ≪≫
    moduleKoszulHomTotalIso f ≪≫ moduleCechTotalIsoAlternatingCechTotal f

end Koszul
