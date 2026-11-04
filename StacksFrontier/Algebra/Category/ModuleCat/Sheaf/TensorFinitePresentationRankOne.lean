module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorFiniteness
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Topologies.FinitePresentationFromCoherence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationTransport

/-!
# Twisting a module of finite presentation by a module locally free of rank one

Let `(C, J, O)` be a ringed site, `Q` a sheaf of `O`-modules of finite presentation in the sense
of Stacks 03DL(7) and `N` a sheaf of `O`-modules which is finite locally free of rank one
(Stacks 0409).  Then `Q ⊗_O N` is of finite presentation.  This is the case of Stacks 03L6 where
one factor is locally trivial; it is proved directly from the definition: over an object on
which `N` is trivial and `Q` has a finite global presentation, `Q ⊗ N` is `Q ⊗ O = Q`.

## Main results

* `Stacks.SheafOfModules.ofArrows_sigma_mem`: composing a covering family with covering families of
  its members gives a covering family.
* `Stacks.SheafOfModules.TensorLocalProperties.isFinitePresentationOnSite_tensor_of_rankOne`: the
  tensor product of a module of finite presentation with a module finite locally free of rank one
  is of finite presentation.

## Implementation notes

The universe-general form of Stacks 03L6 for finite presentation,
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheaf_isFinitePresentation`, is stated for
Mathlib's `SheafOfModules.IsFinitePresentation` and needs the sections of the modules to live in
the universe of the site; neither is available on the small étale site of an algebraic space,
whose objects lie one universe above its sections.  The predicate
`SheafOfModules.IsFinitePresentationOnSite` used here makes no such demand, and the argument only
restricts a trivialization along an arrow of the site and reads off one finite global
presentation.

## References

* [Stacks Project, Tag 03L6](https://stacks.math.columbia.edu/tag/03L6)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u v w

namespace Stacks.SheafOfModules

/-- Composing a covering family of `U` with covering families of each of its members gives a
covering family of `U`. -/
theorem ofArrows_sigma_mem {C : Type*} [Category C] (J : GrothendieckTopology C) {U : C}
    {I : Type*} {V : I → C} (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U)
    {K : I → Type*} {W : ∀ i, K i → C} (g : ∀ i k, W i k ⟶ V i)
    (hg : ∀ i, Sieve.ofArrows (W i) (g i) ∈ J (V i)) :
    Sieve.ofArrows (fun p : Σ i, K i => W p.1 p.2) (fun p => g p.1 p.2 ≫ f p.1) ∈ J U := by
  refine J.transitive hf _ fun Y h hh => ?_
  obtain ⟨Z, e, _, ⟨i⟩, rfl⟩ := hh
  refine J.superset_covering ?_ (J.pullback_stable e (hg i))
  intro T t ht
  obtain ⟨Z', e', _, ⟨k⟩, he'⟩ := ht
  refine ⟨_, e', _, Presieve.ofArrows.mk (⟨i, k⟩ : Σ i, K i), ?_⟩
  simp only
  rw [← Category.assoc, he', Category.assoc]

namespace TensorLocalProperties

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The tensor product of a sheaf of modules with the structure sheaf is the sheaf itself. -/
def sheafTensorUnitIso (O : Sheaf J CommRingCat.{w})
    (M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O).obj M).obj
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))) ≅ M :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).mapIso
      (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit).app M

/-- A sheaf of modules is *locally trivial* when every object has a covering family over each
member of which the module is isomorphic to the structure sheaf. -/
def IsLocallyTrivialOnSite (O : Sheaf J CommRingCat.{w})
    (N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) : Prop :=
  ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ J U ∧ ∀ i, Nonempty (N.over (V i) ≅
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over (V i)))

/-- Over an object on which `N` is trivial, `Q ⊗ N` is `Q`. -/
def tensorOverIsoOfTrivial (O : Sheaf J CommRingCat.{w})
    (Q N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (W : C)
    (e : N.over W ≅
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W)) :
    Q.over W ≅ (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj Q).obj N).over W :=
  (sheafTensorUnitIso (O.over W) (Q.over W)).symm ≪≫
    ((Stacks.SheafOfModules.Tensor.sheafTensor (O.over W)).obj (Q.over W)).mapIso e.symm ≪≫
      tensorOverIso O W Q N

omit [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [∀ (U : C), HasWeakSheafify (J.over U) AddCommGrpCat]
  [∀ (U : C), (J.over U).WEqualsLocallyBijective AddCommGrpCat] in
/-- A covering family on whose members a property `P` of `Q.over -` holds can be refined by a
covering family on whose members `R` holds, provided `P` and triviality of `N` imply `R`. -/
private theorem exists_cover_of_trivial (O : Sheaf J CommRingCat.{w})
    (N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hN : IsLocallyTrivialOnSite O N) (P R : C → Prop)
    (hP : ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, P (V i))
    (hPR : ∀ W, P W → Nonempty (N.over W ≅
      _root_.SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf O).over W)) → R W)
    (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, R (V i) := by
  obtain ⟨I, V, f, hf, hV⟩ := hN U
  choose K W g hg hW using fun i ↦ hP (V i)
  refine ⟨Σ i, K i, fun p ↦ W p.1 p.2, fun p ↦ g p.1 p.2 ≫ f p.1,
    ofArrows_sigma_mem J f hf g hg, fun p ↦ hPR _ (hW p.1 p.2) ?_⟩
  obtain ⟨e⟩ := hV p.1
  exact ⟨(_root_.SheafOfModules.overMap (Stacks.SheafOfModules.Tensor.ringSheaf O)
    (g p.1 p.2)).mapIso e ≪≫ _root_.SheafOfModules.overMapUnitIso (g p.1 p.2)⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Twisting by a locally trivial module preserves and reflects finite presentation**
(Stacks 03L6 with one locally trivial factor). -/
theorem isFinitePresentationOnSite_tensor_iff_of_isLocallyTrivialOnSite
    (O : Sheaf J CommRingCat.{w})
    (Q N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hN : IsLocallyTrivialOnSite O N) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj Q).obj N).IsFinitePresentationOnSite ↔
      Q.IsFinitePresentationOnSite :=
  ⟨fun h ↦ ⟨exists_cover_of_trivial O N hN _ _ h.locally_hasFiniteGlobalPresentation
      fun W _ e ↦ SheafOfModules.HasFiniteGlobalPresentation.of_iso
        (tensorOverIsoOfTrivial O Q N W e.some).symm ‹_›⟩,
    fun h ↦ ⟨exists_cover_of_trivial O N hN _ _ h.locally_hasFiniteGlobalPresentation
      fun W _ e ↦ SheafOfModules.HasFiniteGlobalPresentation.of_iso
        (tensorOverIsoOfTrivial O Q N W e.some) ‹_›⟩⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Twisting by a locally trivial module preserves and reflects quasi-coherence.** -/
theorem isQuasicoherentOnSite_tensor_iff_of_isLocallyTrivialOnSite
    (O : Sheaf J CommRingCat.{w})
    (Q N : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hN : IsLocallyTrivialOnSite O N) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor O).obj Q).obj N).IsQuasicoherentOnSite ↔
      Q.IsQuasicoherentOnSite :=
  ⟨fun h ↦ ⟨exists_cover_of_trivial O N hN _ _ h.locally_hasGlobalPresentation
      fun W _ e ↦ SheafOfModules.HasGlobalPresentation.of_iso
        (tensorOverIsoOfTrivial O Q N W e.some).symm ‹_›⟩,
    fun h ↦ ⟨exists_cover_of_trivial O N hN _ _ h.locally_hasGlobalPresentation
      fun W _ e ↦ SheafOfModules.HasGlobalPresentation.of_iso
        (tensorOverIsoOfTrivial O Q N W e.some) ‹_›⟩⟩

end TensorLocalProperties

end Stacks.SheafOfModules

end
