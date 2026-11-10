module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Filtered.Homology
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import Mathlib.CategoryTheory.Triangulated.LocalizingSubcategory

/-!
# The bounded filtered derived categories

Let `𝒜` be an abelian category, `Fil^f(𝒜)` the additive category of finite filtered objects of
`𝒜` ([Stacks, Tag 05RY]) and `K(Fil^f(𝒜))` the homotopy category of its cochain complexes. A
complex `K^•` of `K(Fil^f(𝒜))` is *filtered acyclic* if every graded piece `gr^p(K^•)` is
acyclic, and a morphism `α` is a *filtered quasi-isomorphism* if every `gr^p(α)` is a
quasi-isomorphism; these form the class `FAc(𝒜)` and the class `FQis(𝒜)`, and the filtered
derived category is `DF(𝒜) = FQis(𝒜)⁻¹K(Fil^f(𝒜))` ([Stacks, Tag 05S2]). Its bounded below, bounded
above and bounded parts `DF⁺(𝒜)`, `DF⁻(𝒜)`, `DFᵇ(𝒜)` are cut out by the vanishing of
`H^n(gr(X))` for `n ≪ 0`, `n ≫ 0`, `|n| ≫ 0` ([Stacks, Tag 05S4]).

In `K⁺(Fil^f(𝒜))`, `K⁻(Fil^f(𝒜))` and `Kᵇ(Fil^f(𝒜))`, and indeed in every triangulated
subcategory `P` of `K(Fil^f(𝒜))`, the filtered acyclic objects form a strictly full saturated
triangulated subcategory whose multiplicative system is `FQis_P(𝒜)`; the functors
`K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)`, `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)`, `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)` have kernels
`FAc⁺(𝒜)`, `FAc⁻(𝒜)`, `FAcᵇ(𝒜)` and are localisations at `FQis⁺(𝒜)`, `FQis⁻(𝒜)`, `FQisᵇ(𝒜)`
([Stacks, Tag 05S6]).

## Main definitions

* `CochainComplex.ofFilteredObjects`: the filtered complex `(K^•, F^p K^•)` attached to a complex
  `K^•` of filtered objects; it is fully faithful, and every filtered complex is in its image
  (`CochainComplex.ofFilteredObjects.toFilteredObjectsIso`).
* `HomotopyCategory.filteredAcyclic`, `HomotopyCategory.filteredQuasiIso`: the classes `FAc(𝒜)`
  and `FQis(𝒜)` of `K(Fil^f(𝒜))`.
* `CochainComplex.FilteredDerivedCategory.Qh`: the localisation functor
  `K(Fil^f(𝒜)) ⥤ DF(𝒜)`.
* `CochainComplex.FilteredDerivedCategory.plus`, `.minus`, `.bounded`: the objects of `DF⁺(𝒜)`,
  `DF⁻(𝒜)`, `DFᵇ(𝒜)`.

## Main results

* `HomotopyCategory.filteredAcyclic_trW`: `FQis(𝒜)` is the class of morphisms whose cone is
  filtered acyclic.
* `CochainComplex.FilteredDerivedCategory.isSaturated_filteredAcyclic_and_isLocalization`:
  [Stacks, Tag 05S6].

## Implementation notes

*Two models of `K(Fil^f(𝒜))`.* `DF(𝒜)` is defined as the localisation of the cochain complexes
of `𝒜` filtered by subcomplexes, with filtration finite in each degree
(`CochainComplex.FilteredDerivedCategory`). Those complexes are the complexes of finite filtered
objects: `CochainComplex.ofFilteredObjects` restricts to an equivalence between
`CochainComplex (FiniteFilteredObject 𝒜) ℤ` and them, under which `gr^p` of the filtered complex
is computed degreewise. The triangulated category `K(Fil^f(𝒜))` of the statement is
`HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)`, triangulated because `Fil^f(𝒜)` is additive.
Filtered homotopy equivalences are filtered quasi-isomorphisms, `gr^p` being additive, so the
localisation functor of `DF(𝒜)` factors through `K(Fil^f(𝒜))` as `Qh`, which is again a
localisation at `FQis(𝒜)`.

*The functors to `DF^±(𝒜)`, `DFᵇ(𝒜)`.* `DF⁺(𝒜)` is the full subcategory of `DF(𝒜)` on the
objects isomorphic to the image of a filtered complex whose associated graded is bounded below
(`CochainComplex.filteredPlus`), and similarly for `DF⁻(𝒜)` and `DFᵇ(𝒜)`. That the comparison
functor `FQis⁺(𝒜)⁻¹K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` is an equivalence is stated as
`Functor.IsLocalization` for the functor `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` itself; that functor is
quantified existentially and pinned by an isomorphism `F ⋙ ι ≅ ι ⋙ Qh`, which determines it up to
a unique isomorphism because `ι` is fully faithful. `K⁺(Fil^f(𝒜))` is
`HomotopyCategory.Plus (FiniteFilteredObject 𝒜)`, and `K⁻(Fil^f(𝒜))`, `Kᵇ(Fil^f(𝒜))` are the
full subcategories on the strict images of the bounded above, resp. bounded, complexes, as in
[Stacks, Tag 05RQ]. The kernel `FAc_P(𝒜)` and the class `FQis_P(𝒜)` are the inverse images along
the inclusion of `P`.

## References

* [Stacks, Tag 05S6](https://stacks.math.columbia.edu/tag/05S6)
* [Stacks, Tag 05S5](https://stacks.math.columbia.edu/tag/05S5)
* [Stacks, Tag 05RW](https://stacks.math.columbia.edu/tag/05RW)
* [Stacks, Tag 05RL](https://stacks.math.columbia.edu/tag/05RL)
-/

@[expose] public section

universe v u

open CategoryTheory Limits Opposite

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-! ### Complexes of filtered objects and filtered complexes -/

namespace ofFilteredObjects

variable (K : CochainComplex (FilteredObject 𝒜 ℤᵒᵖ) ℤ)

/-- The diagram of the filtration steps `F^p K^•` of a complex of filtered objects. -/
noncomputable def diagram : ℤᵒᵖ ⥤ CochainComplex 𝒜 ℤ where
  obj i :=
    { X n := (K.X n).filtration.obj i
      d n m := (K.d n m).natTrans.app i
      shape n m h := by rw [K.shape n m h]; rfl
      d_comp_d' n m l _ _ := by
        change (K.d n m ≫ K.d m l).natTrans.app i = 0
        rw [K.d_comp_d]; rfl }
  map f :=
    { f n := (K.X n).filtration.diagram.map f
      comm' n m _ := (K.d n m).natTrans.naturality f }

/-- The inclusions `F^p K^• ⟶ K^•`. -/
noncomputable def ι : diagram K ⟶ (Functor.const ℤᵒᵖ).obj
    ((FilteredObject.forget).mapHomologicalComplex _ |>.obj K) where
  app i :=
    { f n := (K.X n).filtration.ι.app i
      comm' n m _ := ((K.d n m).comm i).symm }
  naturality i j f := by
    ext n
    exact (K.X n).filtration.ι.naturality f

/-- Each inclusion `F^p K^• ⟶ K^•` is a monomorphism. -/
instance (i : ℤᵒᵖ) : Mono ((ι K).app i) :=
  HomologicalComplex.mono_of_mono_f _ (fun n => inferInstanceAs (Mono ((K.X n).filtration.ι.app i)))

end ofFilteredObjects

open ofFilteredObjects in
/-- The filtered complex `(K^•, F^p K^•)` attached to a complex of filtered objects. -/
noncomputable def ofFilteredObjects :
    CochainComplex (FilteredObject 𝒜 ℤᵒᵖ) ℤ ⥤ FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ where
  obj K := ⟨_, Filtration.ofDiagram (diagram K) (ι K)⟩
  map {K L} φ := FilteredObject.homMk ((FilteredObject.forget).mapHomologicalComplex _ |>.map φ)
    (fun i => { f n := (φ.f n).natTrans.app i
                comm' n m _ := by
                  change (φ.f n ≫ L.d n m).natTrans.app i = (K.d n m ≫ φ.f m).natTrans.app i
                  rw [φ.comm] })
    (fun i => by ext n; exact (φ.f n).comm i)
  map_id K := by ext; rfl
  map_comp f g := by ext; rfl

namespace ofFilteredObjects

/-- `ofFilteredObjects` is faithful. -/
instance : (ofFilteredObjects (𝒜 := 𝒜)).Faithful where
  map_injective {K L} φ ψ h := by
    ext n : 2
    exact congrArg (fun g => g.hom.f n) h

/-- `ofFilteredObjects` is full. -/
instance : (ofFilteredObjects (𝒜 := 𝒜)).Full where
  map_surjective {K L} g :=
    ⟨{ f n := FilteredObject.homMk (g.hom.f n) (fun i => (g.natTrans.app i).f n)
          (fun i => HomologicalComplex.congr_hom (g.comm i) n)
       comm' n m _ := by
         ext
         exact g.hom.comm n m }, by ext; rfl⟩

/-- A filtered complex, seen as a complex of filtered objects. -/
noncomputable def toFilteredObjects (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) :
    CochainComplex (FilteredObject 𝒜 ℤᵒᵖ) ℤ where
  X n := evalFil M n
  d n m := FilteredObject.homMk (M.X.d n m) (fun i => (M.filtration.obj i).d n m)
    (fun i => ((M.filtration.ι.app i).comm n m).symm)
  shape n m h := by ext; exact M.X.shape n m h
  d_comp_d' n m l _ _ := by ext; exact M.X.d_comp_d n m l

/-- Every filtered complex comes from a complex of filtered objects. -/
noncomputable def toFilteredObjectsIso (M : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) :
    ofFilteredObjects.obj (toFilteredObjects M) ≅ M :=
  FilteredObject.isoMk
    (HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) (fun n m _ =>
      (Category.id_comp _).trans (Category.comp_id _).symm))
    (fun i => HomologicalComplex.Hom.isoOfComponents (fun n => Iso.refl _) (fun n m _ =>
      (Category.id_comp _).trans (Category.comp_id _).symm)) (fun i => by
      ext n
      exact (Category.id_comp _).trans (Category.comp_id _).symm)

end ofFilteredObjects

/-- The filtered complexes whose filtration is finite in each degree: the objects of the model of
`K(Fil^f(𝒜))` on which `DF(𝒜)` is defined. -/
abbrev Filf : ObjectProperty (FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) :=
  fun K => ∀ n : ℤ, ∃ p q : ℤ, IsIso ((K.filtration.ι.app (op p)).f n) ∧
    IsZero ((K.filtration.obj (op q)).X n)

/-- A complex of finite filtered objects, as a filtered complex with degreewise finite
filtration. -/
noncomputable def toFilf :
    CochainComplex (FiniteFilteredObject 𝒜) ℤ ⥤ (Filf (𝒜 := 𝒜)).FullSubcategory :=
  ObjectProperty.lift _
    ((ObjectProperty.ι _).mapHomologicalComplex _ ⋙ ofFilteredObjects) (fun K n => by
      obtain ⟨p, hp⟩ := (K.X n).property.exists_isIso_ι
      obtain ⟨q, hq⟩ := (K.X n).property.exists_isZero_obj
      exact ⟨p, q, hp, hq⟩)

/-- `toFilf` is full. -/
instance : (toFilf (𝒜 := 𝒜)).Full := by dsimp [toFilf]; infer_instance
/-- `toFilf` is faithful. -/
instance : (toFilf (𝒜 := 𝒜)).Faithful := by dsimp [toFilf]; infer_instance

/-- A degreewise finite filtered complex, as a complex of finite filtered objects. -/
noncomputable def ofFilf (M : (Filf (𝒜 := 𝒜)).FullSubcategory) :
    CochainComplex (FiniteFilteredObject 𝒜) ℤ where
  X n := ⟨evalFil M.obj n, by
    obtain ⟨p, q, hp, hq⟩ := M.property n
    exact .of_exists ⟨p, hp⟩ ⟨q, hq⟩⟩
  d n m := ObjectProperty.homMk ((ofFilteredObjects.toFilteredObjects M.obj).d n m)
  shape n m h := by ext1; exact (ofFilteredObjects.toFilteredObjects M.obj).shape n m h
  d_comp_d' n m l _ _ := by ext1; exact (ofFilteredObjects.toFilteredObjects M.obj).d_comp_d n m l

/-- A degreewise finite filtered complex `M` is isomorphic to the image of `ofFilf M` under
`toFilf`. -/
noncomputable def toFilfOfFilfIso (M : (Filf (𝒜 := 𝒜)).FullSubcategory) :
    toFilf.obj (ofFilf M) ≅ M :=
  (Filf (𝒜 := 𝒜)).isoMk (ofFilteredObjects.toFilteredObjectsIso M.obj)

/-- Every degreewise finite filtered complex is in the essential image of `toFilf`. -/
instance : (toFilf (𝒜 := 𝒜)).EssSurj := ⟨fun M => ⟨_, ⟨toFilfOfFilfIso M⟩⟩⟩

/-- `toFilf` is an equivalence. -/
instance : (toFilf (𝒜 := 𝒜)).IsEquivalence where

/-! ### Graded pieces -/

section GradedPieces

open FilteredObject

variable (p : ℤ)

/-- The degreewise projections `F^p K^n ⟶ gr^p K^n`, forming a morphism of complexes. -/
noncomputable def grπ (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) :
    (toFilf.obj K).obj.filtration.obj (op p) ⟶
      ((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj K where
  f n := grMapπ (succHom p) (K.X n).obj
  comm' n m _ := grMapπ_map (succHom p) (K.d n m).hom

/-- The step of the filtration at `succHom p` followed by `grπ p K` is zero. -/
lemma grπ_condition (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) :
    (toFilf.obj K).obj.filtration.step (succHom p) ≫ grπ p K = 0 := by
  ext n
  exact step_grMapπ (succHom p) (K.X n).obj

/-- `grπ p K` is a cokernel of the step of the filtration at `succHom p`. -/
noncomputable def isColimitGrπ (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) :
    IsColimit (CokernelCofork.ofπ (grπ p K) (grπ_condition p K)) :=
  HomologicalComplex.isColimitOfEval _ _ (fun n =>
    (isColimitMapCoconeCoforkEquiv' (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) n)
      (grπ_condition p K)).symm (grMapIsCokernel (succHom p) (K.X n).obj :))

/-- `gr^p` of the filtered complex attached to a complex of finite filtered objects is computed
degreewise. -/
noncomputable def grIso :
    toFilf ⋙ (Filf (𝒜 := 𝒜)).ι ⋙ FilteredObject.gr p ≅
      (FiniteFilteredObject.grP p).mapHomologicalComplex (ComplexShape.up ℤ) :=
  NatIso.ofComponents
    (fun K => (grMapIsCokernel (succHom p) (toFilf.obj K).obj).coconePointUniqueUpToIso
      (isColimitGrπ p K)) (fun {K L} φ => by
      apply grMap_hom_ext
      erw [grMapπ_map_assoc]
      erw [IsColimit.comp_coconePointUniqueUpToIso_hom (grMapIsCokernel (succHom p) _)
        (isColimitGrπ p L) WalkingParallelPair.one]
      erw [IsColimit.comp_coconePointUniqueUpToIso_hom_assoc (grMapIsCokernel (succHom p) _)
        (isColimitGrπ p K) WalkingParallelPair.one]
      ext n
      exact (grMapπ_map (succHom p) (φ.f n).hom).symm)

end GradedPieces

end CochainComplex

/-! ### Filtered acyclic complexes and filtered quasi-isomorphisms in `K(Fil^f(𝒜))` -/

section iInf

open Pretriangulated ZeroObject

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] {ι : Type*}

/-- An intersection of strictly full triangulated subcategories is triangulated. -/
lemma ObjectProperty.isTriangulated_iInf (P : ι → ObjectProperty C)
    [∀ i, (P i).IsTriangulated] [∀ i, (P i).IsClosedUnderIsomorphisms] :
    (⨅ i, P i).IsTriangulated where
  exists_zero := ⟨0, isZero_zero C, by
    simp only [iInf_apply, iInf_Prop_eq]; exact fun i => (P i).prop_zero⟩
  isStableUnderShiftBy n := ⟨fun X hX => by
    simp only [ObjectProperty.prop_shift_iff, iInf_apply, iInf_Prop_eq] at hX ⊢
    exact fun i => (P i).le_shift n _ (hX i)⟩
  toIsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ => by
    simp only [iInf_apply, iInf_Prop_eq] at h₁ h₃ ⊢
    exact fun i => (P i).ext_of_isTriangulatedClosed₂ T hT (h₁ i) (h₃ i))

end iInf

namespace HomotopyCategory

variable (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜]

/-- The **filtered acyclic** objects `FAc(𝒜)` of `K(Fil^f(𝒜))`: the complexes `K^•` of finite
filtered objects all of whose graded pieces `gr^p(K^•)` are acyclic. -/
def filteredAcyclic : ObjectProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)) :=
  ⨅ p : ℤ, (subcategoryAcyclic 𝒜).inverseImage
    ((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ))

/-- The **filtered quasi-isomorphisms** `FQis(𝒜)` of `K(Fil^f(𝒜))`: the morphisms `α` such that
every `gr^p(α)` is a quasi-isomorphism. -/
def filteredQuasiIso : MorphismProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)) :=
  fun _ _ α => ∀ p : ℤ, quasiIso 𝒜 (.up ℤ)
    (((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ)).map α)

variable {𝒜}

/-- An object of `K(Fil^f(𝒜))` is filtered acyclic if and only if each of its graded pieces is
acyclic. -/
lemma filteredAcyclic_iff (X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)) :
    filteredAcyclic 𝒜 X ↔ ∀ p : ℤ, subcategoryAcyclic 𝒜
      (((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ)).obj X) := by
  simp [filteredAcyclic]

/-- `FAc(𝒜)` is closed under isomorphisms. -/
instance : (filteredAcyclic 𝒜).IsClosedUnderIsomorphisms := by
  dsimp [filteredAcyclic]; infer_instance

/-- `FAc(𝒜)` is a triangulated subcategory of `K(Fil^f(𝒜))`. -/
instance : (filteredAcyclic 𝒜).IsTriangulated :=
  ObjectProperty.isTriangulated_iInf _

/-- `FAc(𝒜)` is stable under retracts. -/
instance : (filteredAcyclic 𝒜).IsStableUnderRetracts where
  of_retract {X Y} h hY := by
    rw [filteredAcyclic_iff] at hY ⊢
    intro p n
    have r := (h.map ((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ) ⋙
      shiftFunctor _ n ⋙ homologyFunctor 𝒜 (.up ℤ) 0))
    exact (IsZero.iff_id_eq_zero _).2 (by
      refine (r.retract.symm.trans ?_ :)
      rw [(hY p n).eq_zero_of_tgt r.i, zero_comp])

/-- `FQis(𝒜)` is the multiplicative system attached to `FAc(𝒜)` ([Stacks, Tag 05RL]): a
morphism is a filtered quasi-isomorphism if and only if its cone is filtered acyclic. -/
lemma filteredAcyclic_trW : (filteredAcyclic 𝒜).trW = filteredQuasiIso 𝒜 := by
  ext X Y f
  obtain ⟨Z, g, h, hT⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle f
  refine ((filteredAcyclic 𝒜).trW_iff_of_distinguished _ hT).trans ?_
  rw [filteredAcyclic_iff]
  refine forall_congr' fun p => ?_
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  exact ((subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
    (((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ)).map_distinguished _ hT)).symm

end HomotopyCategory

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-! ### The localisation functor `K(Fil^f(𝒜)) ⥤ DF(𝒜)` -/

/-- The filtered quasi-isomorphisms between complexes of finite filtered objects. -/
def filteredQuasiIsoC : MorphismProperty (CochainComplex (FiniteFilteredObject 𝒜) ℤ) :=
  fun _ _ f => ∀ p : ℤ, QuasiIso (((FiniteFilteredObject.grP p).mapHomologicalComplex _).map f)

/-- A morphism of complexes of finite filtered objects is a filtered quasi-isomorphism if and only
if its image under `toFilf` is one. -/
lemma filteredQuasiIso_toFilf_map_iff {K L : CochainComplex (FiniteFilteredObject 𝒜) ℤ}
    (f : K ⟶ L) : filteredQuasiIso 𝒜 (toFilf.map f).hom ↔ filteredQuasiIsoC f :=
  forall_congr' fun p => by
    have e : Arrow.mk ((toFilf ⋙ (Filf (𝒜 := 𝒜)).ι ⋙ FilteredObject.gr p).map f) ≅
      Arrow.mk (((FiniteFilteredObject.grP p).mapHomologicalComplex (.up ℤ)).map f) :=
      Arrow.isoOfNatIso (grIso (𝒜 := 𝒜) p) f
    exact quasiIso_iff_of_arrow_mk_iso _ _ e

/-- The filtered quasi-isomorphisms of degreewise finite filtered complexes. -/
abbrev Wf : MorphismProperty (Filf (𝒜 := 𝒜)).FullSubcategory :=
  (filteredQuasiIso 𝒜).inverseImage (Filf (𝒜 := 𝒜)).ι

/-- `Wf` respects isomorphisms. -/
instance : (Wf (𝒜 := 𝒜)).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun _ _ e hf p =>
    (quasiIso_iff_of_arrow_mk_iso _ _
      (((Filf (𝒜 := 𝒜)).ι ⋙ FilteredObject.gr p).mapArrow.mapIso e)).1 (hf p))

/-- The composite of `toFilf` with the localisation functor at `Wf` is a localisation at
`filteredQuasiIsoC`. -/
lemma isLocalization_toFilf_comp_Q :
    (toFilf ⋙ (Wf (𝒜 := 𝒜)).Q).IsLocalization filteredQuasiIsoC := by
  refine Functor.IsLocalization.of_equivalence_source (Wf (𝒜 := 𝒜)).Q Wf _ _
    toFilf.asEquivalence.symm ?_ ?_
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight toFilf.asEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
  · intro X Y g hg
    refine MorphismProperty.le_isoClosure _ _ ?_
    rw [← filteredQuasiIso_toFilf_map_iff]
    exact ((Wf (𝒜 := 𝒜)).arrow_mk_iso_iff
      (Arrow.isoOfNatIso (toFilf (𝒜 := 𝒜)).asEquivalence.counitIso g)).2 hg
  · intro X Y f hf
    exact Localization.inverts (Wf (𝒜 := 𝒜)).Q (Wf (𝒜 := 𝒜)) ((toFilf (𝒜 := 𝒜)).map f)
      ((filteredQuasiIso_toFilf_map_iff f).2 hf)

/-- Homotopy equivalences of complexes of finite filtered objects are filtered
quasi-isomorphisms. -/
lemma homotopyEquivalences_le_filteredQuasiIsoC :
    HomologicalComplex.homotopyEquivalences _ _ ≤ filteredQuasiIsoC (𝒜 := 𝒜) := by
  rintro K L _ ⟨e, rfl⟩ p
  exact homotopyEquivalences_le_quasiIso _ _ _
    ⟨(FiniteFilteredObject.grP p).mapHomotopyEquiv e, rfl⟩

/-- A morphism of complexes of finite filtered objects is a filtered quasi-isomorphism if and only
if its image in `K(Fil^f(𝒜))` is one. -/
lemma filteredQuasiIso_quotient_map_iff {K L : CochainComplex (FiniteFilteredObject 𝒜) ℤ}
    (f : K ⟶ L) :
    HomotopyCategory.filteredQuasiIso 𝒜 ((HomotopyCategory.quotient _ _).map f) ↔
      filteredQuasiIsoC f :=
  forall_congr' fun p => by
    rw [Functor.mapHomotopyCategory_map]
    exact HomotopyCategory.quotient_map_mem_quasiIso_iff _

/-- `FQis(𝒜)` respects isomorphisms. -/
instance : (HomotopyCategory.filteredQuasiIso 𝒜).RespectsIso :=
  MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun _ _ e hf p =>
    ((HomotopyCategory.quasiIso 𝒜 (.up ℤ)).arrow_mk_iso_iff
      (((FiniteFilteredObject.grP p).mapHomotopyCategory (.up ℤ)).mapArrow.mapIso e)).1 (hf p))

/-- `FQis(𝒜)` is the image of `filteredQuasiIsoC` in `K(Fil^f(𝒜))`. -/
lemma filteredQuasiIso_eq_map :
    HomotopyCategory.filteredQuasiIso 𝒜 =
      (filteredQuasiIsoC (𝒜 := 𝒜)).map (HomotopyCategory.quotient _ _) := by
  ext ⟨K⟩ ⟨L⟩ f
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective f
  constructor
  · intro hf
    exact MorphismProperty.map_mem_map _ _ _ ((filteredQuasiIso_quotient_map_iff f).1 hf)
  · rintro ⟨K', L', g, h, ⟨e⟩⟩
    exact ((HomotopyCategory.filteredQuasiIso 𝒜).arrow_mk_iso_iff e).1
      ((filteredQuasiIso_quotient_map_iff g).2 h)

namespace FilteredDerivedCategory

/-- The localisation functor `Q : K(Fil^f(𝒜)) ⥤ DF(𝒜)`, from the homotopy category of complexes
of finite filtered objects to the filtered derived category. -/
noncomputable def Qh :
    HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ) ⥤ FilteredDerivedCategory 𝒜 :=
  haveI := isLocalization_toFilf_comp_Q (𝒜 := 𝒜)
  Localization.lift (toFilf ⋙ (Wf (𝒜 := 𝒜)).Q)
    (MorphismProperty.IsInvertedBy.of_le _ _ _
      (Localization.inverts _ filteredQuasiIsoC) homotopyEquivalences_le_filteredQuasiIsoC)
    (HomotopyCategory.quotient _ _)

/-- `Qh` is induced by the localisation functor of the filtered complexes. -/
noncomputable def quotientCompQhIso :
    HomotopyCategory.quotient _ _ ⋙ Qh (𝒜 := 𝒜) ≅ toFilf ⋙ (Wf (𝒜 := 𝒜)).Q :=
  haveI := isLocalization_toFilf_comp_Q (𝒜 := 𝒜)
  Localization.fac _ _ _

/-- `Qh` is a localisation of `K(Fil^f(𝒜))` at `FQis(𝒜)`. -/
instance : (Qh (𝒜 := 𝒜)).IsLocalization (HomotopyCategory.filteredQuasiIso 𝒜) := by
  have := isLocalization_toFilf_comp_Q (𝒜 := 𝒜)
  have : (HomotopyCategory.quotient _ _ ⋙ Qh (𝒜 := 𝒜)).IsLocalization filteredQuasiIsoC :=
    Functor.IsLocalization.of_iso _ quotientCompQhIso.symm
  exact Functor.IsLocalization.of_comp (HomotopyCategory.quotient _ _) Qh
    (HomologicalComplex.homotopyEquivalences _ _) (HomotopyCategory.filteredQuasiIso 𝒜)
    filteredQuasiIsoC homotopyEquivalences_le_filteredQuasiIsoC filteredQuasiIso_eq_map

end FilteredDerivedCategory

end CochainComplex

/-! ### Triangulated subcategories of `K(Fil^f(𝒜))` -/

namespace HomotopyCategory

open Pretriangulated

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- A property of objects that is stable under retracts is saturated ([Stacks, Tag 05RB]). -/
lemma isSaturated_of_isStableUnderRetracts {C : Type*} [Category* C] [HasZeroMorphisms C]
    (P : ObjectProperty C) [P.IsStableUnderRetracts] [P.IsClosedUnderIsomorphisms] :
    P.IsSaturated where
  isoClosure_of_biprod_left h := by
    rw [P.isoClosure_eq_self] at h ⊢; exact ObjectProperty.IsStableUnderRetracts.of_biprod_left _ h
  isoClosure_of_biprod_right h := by
    rw [P.isoClosure_eq_self] at h ⊢; exact ObjectProperty.IsStableUnderRetracts.of_biprod_right _ h

variable (P : ObjectProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ))) [P.IsTriangulated]

/-- The filtered acyclic objects of a triangulated subcategory `P` of `K(Fil^f(𝒜))` are stable
under retracts. -/
instance : ((filteredAcyclic 𝒜).inverseImage P.ι).IsStableUnderRetracts where
  of_retract h hY := (filteredAcyclic 𝒜).prop_of_retract (h.map P.ι) hY

/-- In a triangulated subcategory `P` of `K(Fil^f(𝒜))`, a morphism has filtered acyclic cone if and
only if it is a filtered quasi-isomorphism. -/
lemma filteredAcyclic_inverseImage_trW :
    ((filteredAcyclic 𝒜).inverseImage P.ι).trW = (filteredQuasiIso 𝒜).inverseImage P.ι := by
  ext X Y f
  rw [ObjectProperty.inverseImage_trW_iff, filteredAcyclic_trW]
  rfl

/-- The general clause of [Stacks, Tag 05S6], for an arbitrary triangulated subcategory `P` of
`K(Fil^f(𝒜))`. -/
lemma isSaturated_and_kernel_eq {D : Type*} [Category* D] (L : P.FullSubcategory ⥤ D)
    [L.IsLocalization ((filteredQuasiIso 𝒜).inverseImage P.ι)] :
    (((filteredAcyclic 𝒜).inverseImage P.ι).IsClosedUnderIsomorphisms ∧
        ((filteredAcyclic 𝒜).inverseImage P.ι).IsTriangulated ∧
        ((filteredAcyclic 𝒜).inverseImage P.ι).IsSaturated) ∧
      (((filteredQuasiIso 𝒜).inverseImage P.ι).IsSaturated ∧
        ((filteredQuasiIso 𝒜).inverseImage P.ι).IsCompatibleWithTriangulation ∧
        ((filteredAcyclic 𝒜).inverseImage P.ι).trW = (filteredQuasiIso 𝒜).inverseImage P.ι) ∧
      L.kernel = (filteredAcyclic 𝒜).inverseImage P.ι := by
  have hsat := isSaturated_of_isStableUnderRetracts ((filteredAcyclic 𝒜).inverseImage P.ι)
  have heq := filteredAcyclic_inverseImage_trW P
  obtain ⟨⟨-, -, h₁⟩, h₂⟩ :=
    ObjectProperty.hasCalculusOfFractions_isCompatibleWithTriangulation_and_isSaturated_iff
      ((filteredAcyclic 𝒜).inverseImage P.ι) ((filteredQuasiIso 𝒜).inverseImage P.ι)
      (fun X Y f => by
        rw [← heq, ← ObjectProperty.trW_isoClosure]
        exact ⟨fun ⟨Z, g, h, hT, hZ⟩ => ⟨Z, g, h, hT, hZ⟩,
          fun ⟨Z, g, h, hT, hZ⟩ => ⟨Z, g, h, hT, hZ⟩⟩)
  have : L.IsLocalization ((filteredAcyclic 𝒜).inverseImage P.ι).trW := by
    rw [heq]; infer_instance
  exact ⟨⟨inferInstance, inferInstance, hsat⟩, ⟨h₂.2 hsat, h₁, heq⟩,
    ObjectProperty.isLeast_trW_kernel_and_kernel_eq_self.2 _ L⟩

end HomotopyCategory

/-! ### The bounded filtered derived categories -/

namespace CochainComplex

namespace FilteredDerivedCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The objects of the **bounded below filtered derived category** `DF⁺(A)`: those isomorphic to
the image of a degreewise finite filtered complex whose associated graded is bounded below. -/
def plus : ObjectProperty (FilteredDerivedCategory A) :=
  ((filteredPlus A).inverseImage (ObjectProperty.ι _)).map (MorphismProperty.Q _)

/-- The objects of the **bounded above filtered derived category** `DF⁻(A)`: those isomorphic to
the image of a degreewise finite filtered complex whose associated graded is bounded above. -/
def minus : ObjectProperty (FilteredDerivedCategory A) :=
  ((filteredMinus A).inverseImage (ObjectProperty.ι _)).map (MorphismProperty.Q _)

/-- The objects of the **bounded filtered derived category** `DFᵇ(A)`: those isomorphic to the
image of a degreewise finite filtered complex whose associated graded is bounded. -/
def bounded : ObjectProperty (FilteredDerivedCategory A) :=
  ((filteredBounded A).inverseImage (ObjectProperty.ι _)).map (MorphismProperty.Q _)

end FilteredDerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- If `f : K ⟶ L` is a quasi-isomorphism, then `K` is cohomologically `≥ n` if and only if `L`
is. -/
lemma isGE_iff_of_quasiIso {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) [QuasiIso f] (n : ℤ) :
    K.IsGE n ↔ L.IsGE n := by
  simp only [isGE_iff]
  exact forall₂_congr fun i _ => exactAt_iff_of_quasiIsoAt f i

/-- If `f : K ⟶ L` is a quasi-isomorphism, then `K` is cohomologically `≤ n` if and only if `L`
is. -/
lemma isLE_iff_of_quasiIso {K L : CochainComplex 𝒜 ℤ} (f : K ⟶ L) [QuasiIso f] (n : ℤ) :
    K.IsLE n ↔ L.IsLE n := by
  simp only [isLE_iff]
  exact forall₂_congr fun i _ => exactAt_iff_of_quasiIsoAt f i

/-- The graded pieces of a strictly `≥ n` complex of finite filtered objects are strictly `≥ n`. -/
lemma isStrictlyGE_grP (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] (p : ℤ) :
    CochainComplex.IsStrictlyGE
      (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj K) n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact (FiniteFilteredObject.grP p).map_isZero (K.isZero_of_isStrictlyGE n i hi)

/-- The graded pieces of a strictly `≤ n` complex of finite filtered objects are strictly `≤ n`. -/
lemma isStrictlyLE_grP (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (n : ℤ)
    [K.IsStrictlyLE n] (p : ℤ) :
    CochainComplex.IsStrictlyLE
      (((FiniteFilteredObject.grP p).mapHomologicalComplex _).obj K) n := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact (FiniteFilteredObject.grP p).map_isZero (K.isZero_of_isStrictlyLE n i hi)

/-- The complex of finite filtered objects attached to a degreewise finite filtered complex has
the same zero terms. -/
lemma isZero_ofFilf_X (M : (Filf (𝒜 := 𝒜)).FullSubcategory) (n : ℤ)
    (h : IsZero (M.obj.X.X n)) : IsZero ((ofFilf M).X n) :=
  IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _
    ((FilteredObject.isZero_iff _).2 h)

/-- `ofFilf M` is strictly `≥ n` when the underlying complex of `M` is. -/
lemma isStrictlyGE_ofFilf (M : (Filf (𝒜 := 𝒜)).FullSubcategory) (n : ℤ)
    [M.obj.X.IsStrictlyGE n] : (ofFilf M).IsStrictlyGE n := by
  rw [isStrictlyGE_iff]
  intro i hi
  exact isZero_ofFilf_X M i (M.obj.X.isZero_of_isStrictlyGE n i hi)

/-- `ofFilf M` is strictly `≤ n` when the underlying complex of `M` is. -/
lemma isStrictlyLE_ofFilf (M : (Filf (𝒜 := 𝒜)).FullSubcategory) (n : ℤ)
    [M.obj.X.IsStrictlyLE n] : (ofFilf M).IsStrictlyLE n := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact isZero_ofFilf_X M i (M.obj.X.isZero_of_isStrictlyLE n i hi)

/-- If `α : toFilf K ⟶ M` is a filtered quasi-isomorphism, so is the morphism `K ⟶ ofFilf M` it
induces through `toFilfOfFilfIso M`. -/
lemma filteredQuasiIsoC_preimage {K : CochainComplex (FiniteFilteredObject 𝒜) ℤ}
    {M : (Filf (𝒜 := 𝒜)).FullSubcategory} (α : (toFilf.obj K).obj ⟶ M.obj)
    (hα : filteredQuasiIso 𝒜 α) :
    filteredQuasiIsoC (toFilf.preimage (ObjectProperty.homMk α ≫ (toFilfOfFilfIso M).inv)) := by
  rw [← filteredQuasiIso_toFilf_map_iff, Functor.map_preimage]
  exact (MorphismProperty.cancel_right_of_respectsIso (Wf (𝒜 := 𝒜)) _ _).2 hα

/-- If `α : M ⟶ toFilf K` is a filtered quasi-isomorphism, so is the morphism `ofFilf M ⟶ K` it
induces through `toFilfOfFilfIso M`. -/
lemma filteredQuasiIsoC_preimage' {K : CochainComplex (FiniteFilteredObject 𝒜) ℤ}
    {M : (Filf (𝒜 := 𝒜)).FullSubcategory} (α : M.obj ⟶ (toFilf.obj K).obj)
    (hα : filteredQuasiIso 𝒜 α) :
    filteredQuasiIsoC (toFilf.preimage ((toFilfOfFilfIso M).hom ≫ ObjectProperty.homMk α)) := by
  rw [← filteredQuasiIso_toFilf_map_iff, Functor.map_preimage]
  exact (MorphismProperty.cancel_left_of_respectsIso (Wf (𝒜 := 𝒜)) _ _).2 hα

end CochainComplex

namespace CochainComplex.FilteredDerivedCategory

open HomotopyCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-! ### Bounded below complexes -/

/-- The graded pieces of the filtered complex attached to a strictly `≥ n` complex of finite
filtered objects are `≥ n`. -/
private lemma isGE_gr_toFilf (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] (p : ℤ) : ((FilteredObject.gr p).obj (toFilf.obj K).obj).IsGE n := by
  have := isStrictlyGE_grP K n p
  exact isGE_of_iso ((grIso (𝒜 := 𝒜) p).app K).symm n

/-- The graded pieces of the filtered complex attached to a strictly `≤ n` complex of finite
filtered objects are `≤ n`. -/
private lemma isLE_gr_toFilf (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (n : ℤ)
    [K.IsStrictlyLE n] (p : ℤ) : ((FilteredObject.gr p).obj (toFilf.obj K).obj).IsLE n := by
  have := isStrictlyLE_grP K n p
  exact isLE_of_iso ((grIso (𝒜 := 𝒜) p).app K).symm n

/-- The image in `DF(𝒜)` of a strictly bounded below complex of finite filtered objects lies in
`DF⁺(𝒜)`. -/
lemma plus_Qh_obj (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (n : ℤ)
    [K.IsStrictlyGE n] : plus 𝒜 ((Qh (𝒜 := 𝒜)).obj ((HomotopyCategory.quotient _ _).obj K)) :=
  ⟨toFilf.obj K, ⟨n, isGE_gr_toFilf K n⟩,
    ⟨(quotientCompQhIso.app K).symm⟩⟩

/-- `Qh` sends `K⁺(Fil^f(𝒜))` into `DF⁺(𝒜)`. -/
lemma plus_Qh_obj_of_plus {X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)}
    (hX : HomotopyCategory.plus _ X) : plus 𝒜 ((Qh (𝒜 := 𝒜)).obj X) := by
  obtain ⟨K, ⟨n, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact plus_Qh_obj K n

/-- The functor `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` induced by `Qh`. -/
noncomputable abbrev Qplus :
    HomotopyCategory.Plus (FiniteFilteredObject 𝒜) ⥤ (plus 𝒜).FullSubcategory :=
  (plus 𝒜).lift (HomotopyCategory.Plus.ι _ ⋙ Qh) (fun X => plus_Qh_obj_of_plus X.property)

/-- The functor `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` is essentially surjective. -/
instance : (Qplus (𝒜 := 𝒜)).EssSurj where
  mem_essImage Y := by
    obtain ⟨K, ⟨a, ha⟩, ⟨e⟩⟩ := Y.property
    obtain ⟨L, α, hα, hL, hLf⟩ :=
      (exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece _ K.property).1 a ha
    let L' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨L, hLf⟩
    have : L'.obj.X.IsStrictlyGE a := hL
    have := isStrictlyGE_ofFilf L' a
    have : IsIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk α : K ⟶ L')) :=
      Localization.inverts _ (Wf (𝒜 := 𝒜)) _ hα
    refine ⟨⟨(HomotopyCategory.quotient _ _).obj (ofFilf L'),
      (plus_quotient_obj_iff _).2 ⟨a, inferInstance⟩⟩, ⟨(plus 𝒜).isoMk ?_⟩⟩
    exact quotientCompQhIso.app _ ≪≫ (Wf (𝒜 := 𝒜)).Q.mapIso (toFilfOfFilfIso L') ≪≫
      (asIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk α : K ⟶ L'))).symm ≪≫ e

/-- `K⁺(Fil^f(𝒜))` is right localizing with respect to `FAc(𝒜)`, in the sense of Verdier. -/
instance : (HomotopyCategory.plus (FiniteFilteredObject 𝒜)).IsVerdierRightLocalizing
    (HomotopyCategory.filteredAcyclic 𝒜) := by
  rw [ObjectProperty.isVerdierRightLocalizing_iff]
  intro X Y s hX hs
  obtain ⟨K, ⟨a, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  rw [filteredAcyclic_trW, filteredQuasiIso_quotient_map_iff] at hs
  have hM : ∀ p, ((FilteredObject.gr p).obj (toFilf.obj M).obj).IsGE a := fun p => by
    have := hs p
    have := isStrictlyGE_grP K a p
    have := (isGE_iff_of_quasiIso (((FiniteFilteredObject.grP p).mapHomologicalComplex _).map s)
      a).1 inferInstance
    exact isGE_of_iso ((grIso (𝒜 := 𝒜) p).app M).symm a
  obtain ⟨L, α, hα, hL, hLf⟩ :=
    (exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece _ (toFilf.obj M).property).1 a hM
  let L' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨L, hLf⟩
  have : L'.obj.X.IsStrictlyGE a := hL
  have := isStrictlyGE_ofFilf L' a
  have hZ : HomotopyCategory.plus _ ((HomotopyCategory.quotient _ _).obj (ofFilf L')) :=
    (plus_quotient_obj_iff _).2 ⟨a, inferInstance⟩
  have hβ := filteredQuasiIsoC_preimage (M := L') α hα
  have hs' : (HomotopyCategory.filteredAcyclic 𝒜).trW ((HomotopyCategory.quotient _ _).map
      (s ≫ toFilf.preimage (ObjectProperty.homMk α ≫ (toFilfOfFilfIso L').inv))) := by
    rw [filteredAcyclic_trW, filteredQuasiIso_quotient_map_iff]
    intro p
    have := hs p
    have := hβ p
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨W, hW, g, h, hT⟩ := (HomotopyCategory.plus _).distinguished_cocone_triangle
    ((HomotopyCategory.quotient _ _).map
      (s ≫ toFilf.preimage (ObjectProperty.homMk α ≫ (toFilfOfFilfIso L').inv)))
    ((plus_quotient_obj_iff K).2 ⟨a, inferInstance⟩) hZ
  exact ⟨_, _, (HomotopyCategory.quotient _ _).map
      (toFilf.preimage (ObjectProperty.homMk α ≫ (toFilfOfFilfIso L').inv)), hZ,
    ⟨W, g, h, hT, hW, ((HomotopyCategory.filteredAcyclic 𝒜).trW_iff_of_distinguished _ hT).1 hs'⟩,
    (Functor.map_comp _ _ _).symm⟩

/-- The functor `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` is a localisation at `FQis⁺(𝒜)`. -/
lemma isLocalization_Qplus :
    (Qplus (𝒜 := 𝒜)).IsLocalization
      ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage (HomotopyCategory.Plus.ι _)) := by
  have : (Qh (𝒜 := 𝒜)).IsLocalization (HomotopyCategory.filteredAcyclic 𝒜).trW := by
    rw [filteredAcyclic_trW]; infer_instance
  rw [← filteredAcyclic_inverseImage_trW]
  exact ((HomotopyCategory.plus _).triangulatedLocalizerMorphism
    (HomotopyCategory.filteredAcyclic 𝒜)).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := Qh) (F := (plus 𝒜).ι) (ObjectProperty.liftCompιIso _ _ _).symm

/-! ### Bounded above complexes -/

/-- `K⁻(Fil^f(𝒜))`, the objects of `K(Fil^f(𝒜))` represented by a bounded above complex. -/
abbrev Kminus : ObjectProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)) :=
  (CochainComplex.minus _).strictMap (HomotopyCategory.quotient _ (.up ℤ))

/-- `K⁻(Fil^f(𝒜))` is a triangulated subcategory of `K(Fil^f(𝒜))`. -/
instance : (Kminus (𝒜 := 𝒜)).IsTriangulated :=
  (isTriangulated_minus_bounded (FiniteFilteredObject 𝒜)).1

/-- The image in `DF(𝒜)` of a strictly bounded above complex of finite filtered objects lies in
`DF⁻(𝒜)`. -/
lemma minus_Qh_obj (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (n : ℤ)
    [K.IsStrictlyLE n] : minus 𝒜 ((Qh (𝒜 := 𝒜)).obj ((HomotopyCategory.quotient _ _).obj K)) :=
  ⟨toFilf.obj K, ⟨n, isLE_gr_toFilf K n⟩,
    ⟨(quotientCompQhIso.app K).symm⟩⟩

/-- `Qh` sends `K⁻(Fil^f(𝒜))` into `DF⁻(𝒜)`. -/
lemma minus_Qh_obj_of_minus {X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)}
    (hX : Kminus X) : minus 𝒜 ((Qh (𝒜 := 𝒜)).obj X) := by
  obtain ⟨K, ⟨n, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact minus_Qh_obj K n

/-- The functor `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)` induced by `Qh`. -/
noncomputable abbrev Qminus : (Kminus (𝒜 := 𝒜)).FullSubcategory ⥤ (minus 𝒜).FullSubcategory :=
  (minus 𝒜).lift ((Kminus (𝒜 := 𝒜)).ι ⋙ Qh) (fun X => minus_Qh_obj_of_minus X.property)

/-- The image in `K(Fil^f(𝒜))` of a strictly bounded above complex lies in `K⁻(Fil^f(𝒜))`. -/
lemma kminus_quotient_obj {K : CochainComplex (FiniteFilteredObject 𝒜) ℤ} (n : ℤ)
    [K.IsStrictlyLE n] : Kminus ((HomotopyCategory.quotient _ _).obj K) :=
  ObjectProperty.strictMap.mk _ ⟨n, inferInstance⟩

/-- The functor `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)` is essentially surjective. -/
instance : (Qminus (𝒜 := 𝒜)).EssSurj where
  mem_essImage Y := by
    obtain ⟨K, ⟨b, hb⟩, ⟨e⟩⟩ := Y.property
    obtain ⟨L, α, hα, hL, hLf⟩ :=
      (exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece _ K.property).2.1 b hb
    let L' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨L, hLf⟩
    have : L'.obj.X.IsStrictlyLE b := hL
    have := isStrictlyLE_ofFilf L' b
    have : IsIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk α : L' ⟶ K)) :=
      Localization.inverts _ (Wf (𝒜 := 𝒜)) _ hα
    refine ⟨⟨(HomotopyCategory.quotient _ _).obj (ofFilf L'), kminus_quotient_obj b⟩,
      ⟨(minus 𝒜).isoMk ?_⟩⟩
    exact quotientCompQhIso.app _ ≪≫ (Wf (𝒜 := 𝒜)).Q.mapIso (toFilfOfFilfIso L') ≪≫
      asIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk α : L' ⟶ K)) ≪≫ e

/-- `K⁻(Fil^f(𝒜))` is left localizing with respect to `FAc(𝒜)`, in the sense of Verdier. -/
instance : (Kminus (𝒜 := 𝒜)).IsVerdierLeftLocalizing
    (HomotopyCategory.filteredAcyclic 𝒜) := by
  rw [ObjectProperty.isVerdierLeftLocalizing_iff]
  intro X Y s hY hs
  obtain ⟨K, ⟨b, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hY
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨s, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective s
  rw [filteredAcyclic_trW, filteredQuasiIso_quotient_map_iff] at hs
  have hM : ∀ p, ((FilteredObject.gr p).obj (toFilf.obj M).obj).IsLE b := fun p => by
    have := hs p
    have := isStrictlyLE_grP K b p
    have := (isLE_iff_of_quasiIso (((FiniteFilteredObject.grP p).mapHomologicalComplex _).map s)
      b).2 inferInstance
    exact isLE_of_iso ((grIso (𝒜 := 𝒜) p).app M).symm b
  obtain ⟨L, α, hα, hL, hLf⟩ :=
    (exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece _
      (toFilf.obj M).property).2.1 b hM
  let L' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨L, hLf⟩
  have : L'.obj.X.IsStrictlyLE b := hL
  have := isStrictlyLE_ofFilf L' b
  have hZ : Kminus ((HomotopyCategory.quotient _ _).obj (ofFilf L')) := kminus_quotient_obj b
  have hβ := filteredQuasiIsoC_preimage' (M := L') α hα
  have hs' : (HomotopyCategory.filteredAcyclic 𝒜).trW ((HomotopyCategory.quotient _ _).map
      (toFilf.preimage ((toFilfOfFilfIso L').hom ≫ ObjectProperty.homMk α) ≫ s)) := by
    rw [filteredAcyclic_trW, filteredQuasiIso_quotient_map_iff]
    intro p
    have := hs p
    have := hβ p
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨W, hW, g, h, hT⟩ := (Kminus (𝒜 := 𝒜)).distinguished_cocone_triangle
    ((HomotopyCategory.quotient _ _).map
      (toFilf.preimage ((toFilfOfFilfIso L').hom ≫ ObjectProperty.homMk α) ≫ s))
    hZ (kminus_quotient_obj b)
  exact ⟨_, _, (HomotopyCategory.quotient _ _).map
      (toFilf.preimage ((toFilfOfFilfIso L').hom ≫ ObjectProperty.homMk α)), hZ,
    ⟨W, g, h, hT, hW,
      ((HomotopyCategory.filteredAcyclic 𝒜).trW_iff_of_distinguished _ hT).1 hs'⟩,
    (Functor.map_comp _ _ _).symm⟩

/-- The functor `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)` is a localisation at `FQis⁻(𝒜)`. -/
lemma isLocalization_Qminus :
    (Qminus (𝒜 := 𝒜)).IsLocalization
      ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage (Kminus (𝒜 := 𝒜)).ι) := by
  have : (Qh (𝒜 := 𝒜)).IsLocalization (HomotopyCategory.filteredAcyclic 𝒜).trW := by
    rw [filteredAcyclic_trW]; infer_instance
  rw [← filteredAcyclic_inverseImage_trW]
  exact ((Kminus (𝒜 := 𝒜)).triangulatedLocalizerMorphism
    (HomotopyCategory.filteredAcyclic 𝒜)).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := Qh) (F := (minus 𝒜).ι) (ObjectProperty.liftCompιIso _ _ _).symm

end CochainComplex.FilteredDerivedCategory

/-! ### The canonical truncation `τ_{≤ b}` of a filtered complex -/

section TruncLE

open HomologicalComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- `τ_{≤ b}` of a morphism of filtered complexes. -/
noncomputable def truncLEFilteredMap {X Y : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : X ⟶ Y) (b : ℤ) : filteredTruncLE X b ⟶ filteredTruncLE Y b :=
  FilteredObject.homMk (CochainComplex.truncLEMap α.hom b)
    (fun p => CochainComplex.truncLEMap (α.natTrans.app p) b)
    (fun p => by
      change CochainComplex.truncLEMap (α.natTrans.app p) b ≫
            CochainComplex.truncLEMap (Y.filtration.ι.app p) b =
          CochainComplex.truncLEMap (X.filtration.ι.app p) b ≫ CochainComplex.truncLEMap α.hom b
      rw [← HomologicalComplex.truncLEMap_comp, ← HomologicalComplex.truncLEMap_comp, α.comm p])

/-- `τ_{≤ b}` of a morphism of filtered complexes commutes with the inclusions `τ_{≤ b} X ⟶ X`. -/
lemma truncLEFilteredMap_ι {X Y : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ}
    (α : X ⟶ Y) (b : ℤ) :
    truncLEFilteredMap α b ≫ ιFilteredTruncLE Y b = ιFilteredTruncLE X b ≫ α := by
  ext1
  exact CochainComplex.ιTruncLE_naturality α.hom b

/-- The inclusion `τ_{≤ b} X ⟶ X` is an isomorphism when `X` and every step of its filtration are
strictly `≤ b`. -/
lemma isIso_ιFilteredTruncLE (X : FilteredObject (CochainComplex 𝒜 ℤ) ℤᵒᵖ) (b : ℤ)
    [X.X.IsStrictlyLE b] (h : ∀ p : ℤᵒᵖ, (X.filtration.obj p).IsStrictlyLE b) :
    IsIso (ιFilteredTruncLE X b) :=
  (FilteredObject.isIso_iff _).2 ⟨(inferInstance : IsIso (X.X.ιTruncLE b)), fun p => by
    have := h p
    exact (inferInstance : IsIso ((X.filtration.obj p).ιTruncLE b))⟩

end TruncLE

namespace CochainComplex.FilteredDerivedCategory

open HomotopyCategory Pretriangulated

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-! ### Bounded complexes -/

/-- If `Q ≤ P` are triangulated subcategories, the objects of `P` satisfying `Q` form a
triangulated subcategory of `P`. -/
lemma isTriangulated_inverseImage_ι {C : Type*} [Category* C] [HasZeroObject C]
    [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (CategoryTheory.shiftFunctor C n).Additive]
    [CategoryTheory.Pretriangulated C] {P Q : ObjectProperty C} [P.IsTriangulated]
    [Q.IsTriangulated] (h : Q ≤ P) :
    (Q.inverseImage P.ι).IsTriangulated where
  exists_zero := by
    obtain ⟨Z, hZ, hQ⟩ := Q.exists_prop_of_containsZero
    exact ⟨⟨Z, h _ hQ⟩, IsZero.of_full_of_faithful_of_isZero P.ι _ hZ, hQ⟩
  isStableUnderShiftBy n := ⟨fun X hX => by
    have e : P.ι.obj (X⟦n⟧) = (P.ι.obj X)⟦n⟧ := by with_unfolding_all rfl
    change Q (P.ι.obj (X⟦n⟧))
    rw [e]
    exact Q.le_shift n _ hX⟩
  toIsTriangulatedClosed₂ := ⟨fun T hT h₁ h₃ => by
    obtain ⟨Z, hZ, ⟨e⟩⟩ := Q.ext_of_isTriangulatedClosed₂' _ (P.ι.map_distinguished T hT) h₁ h₃
    exact ⟨⟨Z, h _ hZ⟩, hZ, ⟨P.fullyFaithfulι.preimageIso e⟩⟩⟩

/-- `Kᵇ(Fil^f(𝒜))`, the objects of `K(Fil^f(𝒜))` represented by a bounded complex. -/
abbrev Kbounded : ObjectProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)) :=
  (CochainComplex.plus _ ⊓ CochainComplex.minus _).strictMap (HomotopyCategory.quotient _ (.up ℤ))

/-- `Kᵇ(Fil^f(𝒜))` is a triangulated subcategory of `K(Fil^f(𝒜))`. -/
instance : (Kbounded (𝒜 := 𝒜)).IsTriangulated :=
  (isTriangulated_minus_bounded (FiniteFilteredObject 𝒜)).2

/-- `Kᵇ(Fil^f(𝒜))` is contained in `K⁻(Fil^f(𝒜))`. -/
lemma Kbounded_le_Kminus : Kbounded (𝒜 := 𝒜) ≤ Kminus := by
  rintro _ ⟨K, hK⟩
  exact ObjectProperty.strictMap.mk _ hK.2

/-- `Kᵇ(Fil^f(𝒜))` seen inside `K⁻(Fil^f(𝒜))`. -/
abbrev Abd : ObjectProperty (Kminus (𝒜 := 𝒜)).FullSubcategory :=
  (Kbounded (𝒜 := 𝒜)).inverseImage Kminus.ι

/-- The filtered acyclic objects of `K⁻(Fil^f(𝒜))`. -/
abbrev Bm : ObjectProperty (Kminus (𝒜 := 𝒜)).FullSubcategory :=
  (HomotopyCategory.filteredAcyclic 𝒜).inverseImage Kminus.ι

/-- `Kᵇ(Fil^f(𝒜))` is a triangulated subcategory of `K⁻(Fil^f(𝒜))`. -/
instance : (Abd (𝒜 := 𝒜)).IsTriangulated :=
  isTriangulated_inverseImage_ι Kbounded_le_Kminus

/-- The equivalence between `Kᵇ(Fil^f(𝒜))` and its copy `Abd` inside `K⁻(Fil^f(𝒜))`. -/
noncomputable def KboundedEquiv :
    (Kbounded (𝒜 := 𝒜)).FullSubcategory ≌ (Abd (𝒜 := 𝒜)).FullSubcategory :=
  CategoryTheory.Equivalence.mk
    ((Abd (𝒜 := 𝒜)).lift ((Kminus (𝒜 := 𝒜)).lift (Kbounded (𝒜 := 𝒜)).ι
      (fun X => Kbounded_le_Kminus _ X.property)) (fun X => X.property))
    ((Kbounded (𝒜 := 𝒜)).lift ((Abd (𝒜 := 𝒜)).ι ⋙ (Kminus (𝒜 := 𝒜)).ι) (fun X => X.property))
    (Iso.refl _) (Iso.refl _)

/-- The filtered complex attached to a strictly `≤ b` complex of finite filtered objects is
strictly `≤ b`. -/
lemma isStrictlyLE_toFilf_X (M : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (b : ℤ)
    [M.IsStrictlyLE b] : (toFilf.obj M).obj.X.IsStrictlyLE b := by
  rw [isStrictlyLE_iff]
  intro i hi
  exact (FilteredObject.isZero_iff _).1
    ((ObjectProperty.ι _).map_isZero (M.isZero_of_isStrictlyLE b i hi))

/-- Every step of the filtration of the filtered complex attached to a strictly `≤ b` complex of
finite filtered objects is strictly `≤ b`. -/
lemma isStrictlyLE_toFilf_filtration (M : CochainComplex (FiniteFilteredObject 𝒜) ℤ)
    (b : ℤ) [M.IsStrictlyLE b] (p : ℤᵒᵖ) :
    ((toFilf.obj M).obj.filtration.obj p).IsStrictlyLE b := by
  have := isStrictlyLE_toFilf_X M b
  rw [isStrictlyLE_iff]
  intro i hi
  exact IsZero.of_mono (((toFilf.obj M).obj.filtration.ι.app p).f i)
    ((toFilf.obj M).obj.X.isZero_of_isStrictlyLE b i hi)

/-- Inside `K⁻(Fil^f(𝒜))`, `Kᵇ(Fil^f(𝒜))` is right localizing with respect to the filtered acyclic
objects, in the sense of Verdier. -/
instance : (Abd (𝒜 := 𝒜)).IsVerdierRightLocalizing (Bm (𝒜 := 𝒜)) := by
  rw [ObjectProperty.isVerdierRightLocalizing_iff]
  rintro ⟨X, hXm⟩ ⟨Y, hY⟩ s hX hs
  change Kbounded X at hX
  obtain ⟨K, ⟨⟨a, _⟩, ⟨b', _⟩⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  obtain ⟨M, ⟨b, _⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hY
  obtain ⟨s₀, hs₀⟩ := (HomotopyCategory.quotient _ _).map_surjective s.hom
  have hs₁ : filteredQuasiIsoC s₀ := by
    rw [ObjectProperty.inverseImage_trW_iff, filteredAcyclic_trW] at hs
    rwa [← filteredQuasiIso_quotient_map_iff, hs₀]
  have hM : ∀ p, ((FilteredObject.gr p).obj (toFilf.obj M).obj).IsGE a := fun p => by
    have := hs₁ p
    have := isStrictlyGE_grP K a p
    have := (isGE_iff_of_quasiIso (((FiniteFilteredObject.grP p).mapHomologicalComplex _).map s₀)
      a).1 inferInstance
    exact isGE_of_iso ((grIso (𝒜 := 𝒜) p).app M).symm a
  obtain ⟨L, α, hα, hL, hLf⟩ :=
    (exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece _ (toFilf.obj M).property).1 a hM
  have hLb : ∀ p, ((FilteredObject.gr p).obj L).IsLE b := fun p => by
    have := hα p
    have := isStrictlyLE_grP M b p
    have : ((FilteredObject.gr p).obj (toFilf.obj M).obj).IsLE b :=
      isLE_of_iso ((grIso (𝒜 := 𝒜) p).app M).symm b
    exact (isLE_iff_of_quasiIso ((FilteredObject.gr p).map α) b).1 inferInstance
  have hι := filteredQuasiIso_ιFilteredTruncLE L (fun n => by
    obtain ⟨-, q, -, hq⟩ := hLf n
    exact ⟨q, hq⟩) b hLb
  have := isStrictlyLE_toFilf_X M b
  have := isIso_ιFilteredTruncLE (toFilf.obj M).obj b (isStrictlyLE_toFilf_filtration M b)
  have hα' : (inv (ιFilteredTruncLE (toFilf.obj M).obj b) ≫ truncLEFilteredMap α b) ≫
      ιFilteredTruncLE L b = α := by
    rw [Category.assoc, truncLEFilteredMap_ι, IsIso.inv_hom_id_assoc]
  have hα'q : filteredQuasiIso 𝒜
      (inv (ιFilteredTruncLE (toFilf.obj M).obj b) ≫ truncLEFilteredMap α b) := fun p => by
    have := hα p
    have := hι p
    have : QuasiIso ((FilteredObject.gr p).map
        (inv (ιFilteredTruncLE (toFilf.obj M).obj b) ≫ truncLEFilteredMap α b) ≫
          (FilteredObject.gr p).map (ιFilteredTruncLE L b)) := by
      rw [← Functor.map_comp, hα']; infer_instance
    exact quasiIso_of_comp_right _ ((FilteredObject.gr p).map (ιFilteredTruncLE L b))
  let T' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨filteredTruncLE L b, finite_filteredTruncLE L hLf b⟩
  have : L.X.IsStrictlyGE a := hL
  have : T'.obj.X.IsStrictlyLE b := (inferInstance : (L.X.truncLE b).IsStrictlyLE b)
  have : T'.obj.X.IsStrictlyGE a := by
    rw [isStrictlyGE_iff]
    intro i hi
    exact isZero_truncLE_X _ b i (L.X.isZero_of_isStrictlyGE a i hi)
  have := isStrictlyGE_ofFilf T' a
  have := isStrictlyLE_ofFilf T' b
  have hβ := filteredQuasiIsoC_preimage (M := T') _ hα'q
  let Z : (Kminus (𝒜 := 𝒜)).FullSubcategory :=
    ⟨(HomotopyCategory.quotient _ _).obj (ofFilf T'), kminus_quotient_obj b⟩
  have hZ : Abd Z := ObjectProperty.strictMap.mk _ ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩
  let bm : (⟨(HomotopyCategory.quotient _ _).obj M, hY⟩ : (Kminus (𝒜 := 𝒜)).FullSubcategory) ⟶ Z :=
    ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map (toFilf.preimage
      (ObjectProperty.homMk (inv (ιFilteredTruncLE (toFilf.obj M).obj b) ≫
        truncLEFilteredMap α b) ≫ (toFilfOfFilfIso T').inv)))
  have hsb : (Bm (𝒜 := 𝒜)).trW (s ≫ bm) := by
    rw [ObjectProperty.inverseImage_trW_iff, filteredAcyclic_trW]
    change HomotopyCategory.filteredQuasiIso 𝒜 (s.hom ≫ (HomotopyCategory.quotient _ _).map _)
    rw [← hs₀, ← Functor.map_comp, filteredQuasiIso_quotient_map_iff]
    intro p
    have := hs₁ p
    have := hβ p
    rw [Functor.map_comp]
    infer_instance
  obtain ⟨W, hW, g, h, hT⟩ := (Abd (𝒜 := 𝒜)).distinguished_cocone_triangle (s ≫ bm) hX hZ
  exact ⟨Z, s ≫ bm, bm, hZ,
    ⟨W, g, h, hT, hW, ((Bm (𝒜 := 𝒜)).trW_iff_of_distinguished _ hT).1 hsb⟩, rfl⟩

/-- The image in `DF(𝒜)` of a strictly bounded complex of finite filtered objects lies in
`DFᵇ(𝒜)`. -/
lemma bounded_Qh_obj (K : CochainComplex (FiniteFilteredObject 𝒜) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [K.IsStrictlyLE b] :
    bounded 𝒜 ((Qh (𝒜 := 𝒜)).obj ((HomotopyCategory.quotient _ _).obj K)) :=
  ⟨toFilf.obj K, ⟨⟨a, isGE_gr_toFilf K a⟩, ⟨b, isLE_gr_toFilf K b⟩⟩,
    ⟨(quotientCompQhIso.app K).symm⟩⟩

/-- `Qh` sends `Kᵇ(Fil^f(𝒜))` into `DFᵇ(𝒜)`. -/
lemma bounded_Qh_obj_of_bounded {X : HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ)}
    (hX : Kbounded X) : bounded 𝒜 ((Qh (𝒜 := 𝒜)).obj X) := by
  obtain ⟨K, ⟨⟨a, _⟩, ⟨b, _⟩⟩, rfl⟩ := (ObjectProperty.strictMap_iff _ _ _).1 hX
  exact bounded_Qh_obj K a b

/-- The functor `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)` induced by `Qh`. -/
noncomputable abbrev Qbounded :
    (Kbounded (𝒜 := 𝒜)).FullSubcategory ⥤ (bounded 𝒜).FullSubcategory :=
  (bounded 𝒜).lift ((Kbounded (𝒜 := 𝒜)).ι ⋙ Qh) (fun X => bounded_Qh_obj_of_bounded X.property)

/-- The functor `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)` is essentially surjective. -/
instance : (Qbounded (𝒜 := 𝒜)).EssSurj where
  mem_essImage Y := by
    obtain ⟨K, ⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨e⟩⟩ := Y.property
    obtain ⟨L, M, N, f, g, h, i, -, hf, hg, -, -, -, -, hN₁, hN₂, -, hMf, hNf⟩ :=
      (exists_filteredQuasiIso_bounded_of_isGE_of_isLE_gradedPiece _ K.property).2.2 a b ha hb
    let M' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨M, hMf⟩
    let N' : (Filf (𝒜 := 𝒜)).FullSubcategory := ⟨N, hNf⟩
    have := isStrictlyGE_ofFilf N' a
    have := isStrictlyLE_ofFilf N' b
    have : IsIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk f : M' ⟶ K)) :=
      Localization.inverts _ (Wf (𝒜 := 𝒜)) _ hf
    have : IsIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk g : M' ⟶ N')) :=
      Localization.inverts _ (Wf (𝒜 := 𝒜)) _ hg
    refine ⟨⟨(HomotopyCategory.quotient _ _).obj (ofFilf N'),
      ObjectProperty.strictMap.mk _ ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩⟩,
      ⟨(bounded 𝒜).isoMk ?_⟩⟩
    exact quotientCompQhIso.app _ ≪≫ (Wf (𝒜 := 𝒜)).Q.mapIso (toFilfOfFilfIso N') ≪≫
      (asIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk g : M' ⟶ N'))).symm ≪≫
      asIso ((Wf (𝒜 := 𝒜)).Q.map (ObjectProperty.homMk f : M' ⟶ K)) ≪≫ e

/-- `DFᵇ(𝒜)` is contained in `DF⁻(𝒜)`. -/
lemma bounded_le_minus : bounded 𝒜 ≤ minus 𝒜 := by
  rintro _ ⟨K, hK, e⟩
  exact ⟨K, hK.2, e⟩

/-- The functor `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)` is a localisation at `FQisᵇ(𝒜)`. -/
lemma isLocalization_Qbounded :
    (Qbounded (𝒜 := 𝒜)).IsLocalization
      ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage (Kbounded (𝒜 := 𝒜)).ι) := by
  have h₂ : (Qminus (𝒜 := 𝒜)).IsLocalization (Bm (𝒜 := 𝒜)).trW := by
    rw [filteredAcyclic_inverseImage_trW]
    exact isLocalization_Qminus
  have : (KboundedEquiv.inverse ⋙ Qbounded (𝒜 := 𝒜)).EssSurj := inferInstance
  have h₁ : (KboundedEquiv.inverse ⋙ Qbounded (𝒜 := 𝒜)).IsLocalization
      ((Bm (𝒜 := 𝒜)).inverseImage (Abd (𝒜 := 𝒜)).ι).trW :=
    (ObjectProperty.triangulatedLocalizerMorphism _ _).isLocalization_of_isLocalizedFullyFaithful
      (L₂ := Qminus) (F := ObjectProperty.ιOfLE bounded_le_minus) (Iso.refl _)
  refine Functor.IsLocalization.of_equivalence_source
    (KboundedEquiv.inverse ⋙ Qbounded (𝒜 := 𝒜)) ((Bm (𝒜 := 𝒜)).inverseImage (Abd (𝒜 := 𝒜)).ι).trW
    _ _ KboundedEquiv.symm ?_ ?_ (Iso.refl _)
  · intro X Y f hf
    rw [ObjectProperty.inverseImage_trW_iff, ObjectProperty.inverseImage_trW_iff,
      filteredAcyclic_trW] at hf
    exact MorphismProperty.le_isoClosure _ _ hf
  · intro X Y f hf
    have h : IsIso ((bounded 𝒜).ι.map ((Qbounded (𝒜 := 𝒜)).map f)) :=
      Localization.inverts (Qh (𝒜 := 𝒜)) (HomotopyCategory.filteredQuasiIso 𝒜) _ hf
    exact isIso_of_reflects_iso _ (bounded 𝒜).ι

end CochainComplex.FilteredDerivedCategory

namespace CochainComplex.FilteredDerivedCategory

open HomotopyCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-! ### The theorem -/

/-- Let `𝒜` be an abelian category. For every triangulated subcategory `P` of `K(Fil^f(𝒜))` — in
particular for `K⁺(Fil^f(𝒜))`, `K⁻(Fil^f(𝒜))` and `Kᵇ(Fil^f(𝒜))` — the filtered acyclic objects
`FAc_P(𝒜)` of `P` form a strictly full saturated triangulated subcategory of `P`, the filtered
quasi-isomorphisms `FQis_P(𝒜)` of `P` form a saturated multiplicative system compatible with the
triangulation which is the class `FAc_P(𝒜).trW` corresponding to `FAc_P(𝒜)` under
[Stacks, Tag 05RL], and the kernel of any localisation of `P` at `FQis_P(𝒜)` is `FAc_P(𝒜)`.
Moreover:

1. the functor `K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` induced by `Qh : K(Fil^f(𝒜)) ⥤ DF(𝒜)` has kernel
   `FAc⁺(𝒜)` and is a localisation at `FQis⁺(𝒜)`, so that
   `K⁺(Fil^f(𝒜))/FAc⁺(𝒜) = FQis⁺(𝒜)⁻¹K⁺(Fil^f(𝒜)) ⥤ DF⁺(𝒜)` is an equivalence;
2. the functor `K⁻(Fil^f(𝒜)) ⥤ DF⁻(𝒜)` induced by `Qh` has kernel `FAc⁻(𝒜)` and is a
   localisation at `FQis⁻(𝒜)`;
3. the functor `Kᵇ(Fil^f(𝒜)) ⥤ DFᵇ(𝒜)` induced by `Qh` has kernel `FAcᵇ(𝒜)` and is a
   localisation at `FQisᵇ(𝒜)`. -/
@[stacks 05S6]
public theorem isSaturated_filteredAcyclic_and_isLocalization :
    (∀ (P : ObjectProperty (HomotopyCategory (FiniteFilteredObject 𝒜) (.up ℤ))) [P.IsTriangulated]
        {D : Type*} [Category* D] (L : P.FullSubcategory ⥤ D)
        [L.IsLocalization ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage P.ι)],
      (((HomotopyCategory.filteredAcyclic 𝒜).inverseImage P.ι).IsClosedUnderIsomorphisms ∧
          ((HomotopyCategory.filteredAcyclic 𝒜).inverseImage P.ι).IsTriangulated ∧
          ((HomotopyCategory.filteredAcyclic 𝒜).inverseImage P.ι).IsSaturated) ∧
        (((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage P.ι).IsSaturated ∧
          ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage P.ι).IsCompatibleWithTriangulation ∧
          ((HomotopyCategory.filteredAcyclic 𝒜).inverseImage P.ι).trW =
            (HomotopyCategory.filteredQuasiIso 𝒜).inverseImage P.ι) ∧
        L.kernel = (HomotopyCategory.filteredAcyclic 𝒜).inverseImage P.ι) ∧
    (∃ F : HomotopyCategory.Plus (FiniteFilteredObject 𝒜) ⥤ (plus 𝒜).FullSubcategory,
      Nonempty (F ⋙ (plus 𝒜).ι ≅ HomotopyCategory.Plus.ι _ ⋙ Qh) ∧
        F.IsLocalization ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage
          (HomotopyCategory.Plus.ι _)) ∧
        F.kernel = (HomotopyCategory.filteredAcyclic 𝒜).inverseImage (HomotopyCategory.Plus.ι _)) ∧
    (∃ F : ((CochainComplex.minus _).strictMap
          (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).FullSubcategory ⥤
        (minus 𝒜).FullSubcategory,
      Nonempty (F ⋙ (minus 𝒜).ι ≅ ((CochainComplex.minus _).strictMap
          (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).ι ⋙ Qh) ∧
        F.IsLocalization ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage
          ((CochainComplex.minus _).strictMap
            (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).ι) ∧
        F.kernel = (HomotopyCategory.filteredAcyclic 𝒜).inverseImage
          ((CochainComplex.minus _).strictMap
            (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).ι) ∧
    (∃ F : ((CochainComplex.plus _ ⊓ CochainComplex.minus _).strictMap
          (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).FullSubcategory ⥤
        (bounded 𝒜).FullSubcategory,
      Nonempty (F ⋙ (bounded 𝒜).ι ≅ ((CochainComplex.plus _ ⊓ CochainComplex.minus _).strictMap
          (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).ι ⋙ Qh) ∧
        F.IsLocalization ((HomotopyCategory.filteredQuasiIso 𝒜).inverseImage
          ((CochainComplex.plus _ ⊓ CochainComplex.minus _).strictMap
            (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).ι) ∧
        F.kernel = (HomotopyCategory.filteredAcyclic 𝒜).inverseImage
          ((CochainComplex.plus _ ⊓ CochainComplex.minus _).strictMap
            (HomotopyCategory.quotient (FiniteFilteredObject 𝒜) (.up ℤ))).ι) := by
  have := isLocalization_Qplus (𝒜 := 𝒜)
  have := isLocalization_Qminus (𝒜 := 𝒜)
  have := isLocalization_Qbounded (𝒜 := 𝒜)
  exact ⟨fun P _ D _ L _ => isSaturated_and_kernel_eq P L,
    ⟨Qplus, ⟨ObjectProperty.liftCompιIso _ _ _⟩, isLocalization_Qplus,
      (isSaturated_and_kernel_eq _ Qplus).2.2⟩,
    ⟨Qminus, ⟨ObjectProperty.liftCompιIso _ _ _⟩, isLocalization_Qminus,
      (isSaturated_and_kernel_eq _ Qminus).2.2⟩,
    ⟨Qbounded, ⟨ObjectProperty.liftCompιIso _ _ _⟩, isLocalization_Qbounded,
      (isSaturated_and_kernel_eq _ Qbounded).2.2⟩⟩

end CochainComplex.FilteredDerivedCategory
