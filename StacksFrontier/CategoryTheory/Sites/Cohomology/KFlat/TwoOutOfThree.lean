module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.TensorOfAShortExactSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
import StacksCore.Tactic.StacksAttribute

/-! # Two out of three for K-flatness in a short exact sequence of complexes

Let `(C, O)` be a ringed site and let `0 → K₁ → K₂ → K₃ → 0` be a short exact sequence of
complexes of `O`-modules whose third term has flat terms. If two of the three complexes are
K-flat, so is the third. This is Stacks 0G7B.

The proof is the one in the source. For every complex `L` the sequence of total complexes
`0 → Tot(L ⊗ K₁) → Tot(L ⊗ K₂) → Tot(L ⊗ K₃) → 0` is short exact: in each degree `n` it is the
direct sum over `p + q = n` of the sequences `0 → L^p ⊗ K₁^q → L^p ⊗ K₂^q → L^p ⊗ K₃^q → 0`, each
of which is short exact by Stacks 03EX (2), since `K₃^q` is flat; and a direct sum of short exact
sequences is short exact because coproducts are exact in the category of sheaves of modules
(AB4, from Tag 03DB). The conclusion then follows from the long exact sequence of cohomology
sheaves: if two of three complexes in a short exact sequence are acyclic, so is the third.

## Main results

* `Stacks.SheafOfModules.shortExact_map_tensorComplex`: the sequence of total complexes is short
  exact.
* `Stacks.SheafOfModules.isKFlat_X₁`, `isKFlat_X₂`, `isKFlat_X₃`: the three directions.
* `Stacks.SheafOfModules.isKFlat_two_out_of_three`: Stacks 0G7B.

## Implementation notes

The degree-`n` object of a total complex is a coproduct indexed by the fibre of the total
complex shape, exhibited by `CategoryTheory.GradedObject.cofanMapObj` together with
`GradedObject.isColimitCofanMapObj`, and the degree-`n` component of a map of total complexes is
compatible with those inclusions by `HomologicalComplex.ι_mapBifunctorMap`. That is what lets
Mathlib's `CategoryTheory.Limits.colim.map_mono'`, `colim.map_epi'` and
`colim.exact_mapShortComplex` be applied to a cofan rather than to the chosen coproduct, so no
transport along a coproduct comparison is needed.

Exactness of the three-term sequence of diagrams over `Discrete (fibre)` is checked objectwise
through `CategoryTheory.JointlyReflectIsomorphisms.exact_iff` for the evaluation functors.

The coproducts here are indexed by a subtype of `ℤ × ℤ`, so AB4 is needed only at size `0`; it is
obtained from the AB5 property of sheaves of modules (Tag 03DB) by `AB5OfSize_shrink` and
`AB4.of_AB5`, which is the same route as `Stacks.SheafOfModules.kFlat_colimit` (Tag 06YE) takes.

The universes are collapsed to `RingedSite.{u, u, u}` because Stacks 03EX (2) is: see the
implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/TensorOfAShortExactSequence.lean`.

## References

* [Stacks Project, Tag 0G7B](https://stacks.math.columbia.edu/tag/0G7B)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 06Y9](https://stacks.math.columbia.edu/tag/06Y9)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.SheafOfModules

section Acyclic

variable {A : Type*} [Category* A] [Abelian A]

/-- In a short exact sequence of complexes, if the middle and the right complex are acyclic, so
is the left one: the long exact sequence of cohomology gives exactness of
`H^{j-1}(X₃) → H^j(X₁) → H^j(X₂)`, whose outer terms vanish. -/
alias acyclic_X₁_of_acyclic_X₂_X₃ :=
  Stacks.SheafOfModules.KFlatTwoOutOfThree.acyclic_X₁_of_shortExact

/-- In a short exact sequence of complexes, if the left and the middle complex are acyclic, so is
the right one: the long exact sequence of cohomology gives exactness of
`H^i(X₂) → H^i(X₃) → H^{i+1}(X₁)`, whose outer terms vanish. -/
alias acyclic_X₃_of_acyclic_X₁_X₂ :=
  Stacks.SheafOfModules.KFlatTwoOutOfThree.acyclic_X₃_of_shortExact

end Acyclic

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category of sheaves of modules on the ringed site, abbreviated. -/
abbrev ModO := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)

/-- Coproducts indexed by a type in `Type 0` are exact in sheaves of modules: AB5 (Tag 03DB)
shrinks to size `0` and implies AB4 there. -/
lemma hasExactColimitsOfShape_discrete (β : Type) :
    HasExactColimitsOfShape (Discrete β) (ModO X) := by
  have : AB5OfSize.{u, u} (ModO X) :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)
  have : AB5OfSize.{0, 0} (ModO X) := AB5OfSize_shrink (ModO X)
  have : HasFiniteBiproducts (ModO X) := HasFiniteBiproducts.of_hasFiniteProducts
  have : AB4OfSize.{0} (ModO X) := AB4.of_AB5 _
  exact AB4OfSize.ofShape β

variable
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- The total tensor complex functor `Tot(L ⊗ -)` is additive, hence preserves zero
morphisms, which is what lets it be applied to a short complex. -/
instance additive_tensorComplex_obj
    (L : CochainComplex (ModO X) ℤ) : ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj
      L).Additive :=
  Stacks.SheafOfModules.Tensor.Reduction.map₂HomologicalComplex_obj_additive
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L

section Degreewise

variable (L : CochainComplex (ModO X) ℤ)

/-- The fibre of the total complex shape over `n`, indexing the summands of degree `n`. -/
abbrev fibre (n : ℤ) : Type :=
  {pq : ℤ × ℤ //
    ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) pq = n}

/-- The double complex `(p, q) ↦ L^p ⊗ T^q` whose total complex is `Tot(L ⊗ T)`. -/
noncomputable abbrev bicx (T : CochainComplex (ModO X) ℤ) :
    HomologicalComplex₂ (ModO X) (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).mapBifunctorHomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj L).obj T

/-- The family of summands `L^p ⊗ T^q` of the degree-`n` part of `Tot(L ⊗ T)`. -/
noncomputable abbrev summands (T : CochainComplex (ModO X) ℤ) (n : ℤ) :
    fibre n → ModO X :=
  (bicx X L T).toGradedObject.mapObjFun
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n

/-- The cofan exhibiting the degree-`n` part of `Tot(L ⊗ T)` as the direct sum of its
summands. -/
noncomputable def totalCofan (T : CochainComplex (ModO X) ℤ) (n : ℤ) :
    Cofan (summands X L T n) :=
  (bicx X L T).toGradedObject.cofanMapObj
    (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) n

/-- The cofan of `totalCofan` is a colimit. -/
noncomputable def totalCofanIsColimit (T : CochainComplex (ModO X) ℤ) (n : ℤ) :
    IsColimit (totalCofan X L T n) :=
  (bicx X L T).toGradedObject.isColimitCofanMapObj _ n

/-- The diagram of summands over the discrete fibre. -/
noncomputable abbrev summandsFunctor (T : CochainComplex (ModO X) ℤ) (n : ℤ) :
    Discrete (fibre n) ⥤ ModO X :=
  Discrete.functor (summands X L T n)

/-- The summandwise map induced by a morphism of complexes. -/
noncomputable def summandsMap {T T' : CochainComplex (ModO X) ℤ} (f : T ⟶ T')
    (n : ℤ) : summandsFunctor X L T n ⟶ summandsFunctor X L T' n :=
  Discrete.natTrans fun b =>
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.as.1.1)).map (f.f b.as.1.2)

/-- The degree-`n` component of `Tot(L ⊗ -)` applied to a morphism is compatible with the
inclusions of the summands. -/
lemma totalCofan_inj_comp {T T' : CochainComplex (ModO X) ℤ} (f : T ⟶ T') (n : ℤ)
    (j : Discrete (fibre n)) :
    (totalCofan X L T n).ι.app j ≫ (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L).map
      f).f n =
      (summandsMap X L f n).app j ≫ (totalCofan X L T' n).ι.app j := by
  obtain ⟨⟨⟨p, q⟩, hpq⟩⟩ := j
  have h := HomologicalComplex.ι_mapBifunctorMap (𝟙 L) f
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) p q n hpq
  rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at h
  exact h

variable (S : ShortComplex (CochainComplex (ModO X) ℤ))

omit [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Each summand of the degree-`n` sequence is short exact: this is Stacks 03EX (2) applied to
the degree-`q` part of the sequence, whose third term is flat. -/
lemma shortExact_summand (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.O) (S.X₃.X i))
    (n : ℤ) (b : fibre n) :
    ((S.map (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) b.1.2)).map
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1))).ShortExact := by
  have hq : (S.map (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) b.1.2)).ShortExact :=
    hS.map_of_exact _
  exact shortExact_map_sheafTensorObj X _ hq (hflat b.1.2) _

/-- The three-term sequence of diagrams of summands. -/
noncomputable def summandsShortComplex (n : ℤ) :
    ShortComplex (Discrete (fibre n) ⥤ ModO X) :=
  ShortComplex.mk (summandsMap X L S.f n) (summandsMap X L S.g n) (by
    refine NatTrans.ext (funext fun j => ?_)
    change ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X j.as.1.1)).map (S.f.f j.as.1.2)
      ≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X j.as.1.1)).map (S.g.f j.as.1.2) = 0
    rw [← Functor.map_comp, ← HomologicalComplex.comp_f, S.zero,
      HomologicalComplex.zero_f, Functor.map_zero])

omit [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Exactness in the diagram category is objectwise. -/
lemma summandsShortComplex_exact (n : ℤ)
    (hb : ∀ b : fibre n,
      ((S.map (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) b.1.2)).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1))).ShortExact) :
    (summandsShortComplex X L S n).Exact := by
  have hjr : JointlyReflectIsomorphisms
      (fun j : Discrete (fibre n) =>
        (evaluation (Discrete (fibre n)) (ModO X)).obj j) :=
    ⟨fun f h => by
      have : ∀ j, IsIso (f.app j) := h
      exact NatIso.isIso_of_isIso_app f⟩
  refine (hjr.exact_iff _).2 fun j => ?_
  exact (hb j.as).exact

/-- The degree-`n` part of the sequence of total complexes is short exact, given that each
summand sequence is. -/
lemma shortExact_degreewise (n : ℤ)
    (hb : ∀ b : fibre n,
      ((S.map (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) b.1.2)).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1))).ShortExact) :
    ((S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L)).map
      (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) n)).ShortExact := by
  have : HasExactColimitsOfShape (Discrete (fibre n)) (ModO X) :=
    hasExactColimitsOfShape_discrete X (fibre n)
  have hmono : ∀ j, Mono ((summandsMap X L S.f n).app j) := fun j => (hb j.as).mono_f
  have hepi : ∀ j, Epi ((summandsMap X L S.g n).app j) := fun j => (hb j.as).epi_g
  have : Mono (summandsMap X L S.f n) := NatTrans.mono_of_mono_app _
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · exact colim.exact_mapShortComplex (summandsShortComplex_exact X L S n hb)
      (totalCofanIsColimit X L S.X₁ n) (totalCofanIsColimit X L S.X₂ n)
      (totalCofanIsColimit X L S.X₃ n) _ _
      (totalCofan_inj_comp X L S.f n) (totalCofan_inj_comp X L S.g n)
  · exact colim.map_mono' (summandsMap X L S.f n)
      (totalCofanIsColimit X L S.X₁ n) (totalCofanIsColimit X L S.X₂ n) _
      (totalCofan_inj_comp X L S.f n)
  · exact colim.map_epi' (summandsMap X L S.g n)
      (totalCofan X L S.X₂ n) (totalCofanIsColimit X L S.X₃ n) _
      (totalCofan_inj_comp X L S.g n)

/-- The sequence of total complexes is short exact once every summand sequence is. -/
private theorem shortExact_map_tensorComplex_of_summands
    (hb : ∀ (n : ℤ) (b : fibre n),
      ((S.map (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) b.1.2)).map
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1))).ShortExact) :
    (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    fun n => shortExact_degreewise X L S n (hb n)

/-- **Stacks 03EX (2) for complexes.** Tensoring a short exact sequence of complexes of sheaves
of modules whose third term has flat terms with any complex gives a short exact sequence of
total complexes. -/
theorem shortExact_map_tensorComplex (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.O) (S.X₃.X i)) :
    (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L)).ShortExact :=
  shortExact_map_tensorComplex_of_summands X L S (shortExact_summand X L S hS hflat)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- Each summand of the degree-`n` sequence is short exact also when it is the *fixed* tensor
factor `L` that has flat terms, the sequence `S` then being arbitrary: tensoring on the left with
a flat sheaf of modules is an exact functor.

The additivity and `HasMapBifunctor` section instances are omitted because this statement is
about a single degree, where the total complex — and so the bifunctor's mapping property —
never appears. -/
lemma shortExact_summand_of_isFlat_terms (hS : S.ShortExact)
    (hL : ∀ p : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (L.X p))
    (n : ℤ) (b : fibre n) :
    ((S.map (HomologicalComplex.eval (ModO X) (ComplexShape.up ℤ) b.1.2)).map
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1))).ShortExact := by
  have hex : exactFunctor _ _ ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1)) :=
    exact_sheafTensorObj_of_isFlat.{u, u, u} X.O (hL b.1.1)
  have : PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1)) :=
    ((exactFunctor_iff _).1 hex).1
  have : PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X b.1.1)) :=
    ((exactFunctor_iff _).1 hex).2
  exact (hS.map_of_exact _).map_of_exact _

/-- **Tot of a flat-termed complex is exact.** If the fixed tensor factor `L` has flat terms,
then `Tot(L ⊗ -)` carries every short exact sequence of complexes to a short exact sequence,
with no condition on the sequence. -/
theorem shortExact_map_tensorComplex_of_isFlat_terms (hS : S.ShortExact)
    (hL : ∀ p : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O) (L.X p)) :
    (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L)).ShortExact :=
  shortExact_map_tensorComplex_of_summands X L S (shortExact_summand_of_isFlat_terms X L S hS hL)

end Degreewise

section TwoOutOfThree

variable (S : ShortComplex (CochainComplex (ModO X) ℤ)) (hS : S.ShortExact)
    (hflat : ∀ i : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := X.O) (S.X₃.X i))

include hS hflat

/-- If the outer two complexes of the sequence are K-flat, so is the right one. -/
theorem isKFlat_X₃ (h₁ : IsKFlat X.O S.X₁) (h₂ : IsKFlat X.O S.X₂) : IsKFlat X.O S.X₃ := by
  intro L hL
  exact acyclic_X₃_of_acyclic_X₁_X₂ (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L))
    (shortExact_map_tensorComplex X L S hS hflat) (h₁ L hL) (h₂ L hL)

/-- If the outer two complexes of the sequence are K-flat, so is the middle one. -/
theorem isKFlat_X₂ (h₁ : IsKFlat X.O S.X₁) (h₃ : IsKFlat X.O S.X₃) : IsKFlat X.O S.X₂ := by
  intro L hL
  exact (shortExact_map_tensorComplex X L S hS hflat).acyclic_X₂ (h₁ L hL) (h₃ L hL)

/-- If the right two complexes of the sequence are K-flat, so is the left one. -/
theorem isKFlat_X₁ (h₂ : IsKFlat X.O S.X₂) (h₃ : IsKFlat X.O S.X₃) : IsKFlat X.O S.X₁ := by
  intro L hL
  exact acyclic_X₁_of_acyclic_X₂_X₃ (S.map ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj L))
    (shortExact_map_tensorComplex X L S hS hflat) (h₂ L hL) (h₃ L hL)

/-- **Stacks 0G7B.** In a short exact sequence of complexes of sheaves of modules on a ringed
site whose third term has flat terms, if two out of the three complexes are K-flat, so is the
third. -/
@[stacks 0G7B]
theorem isKFlat_two_out_of_three
    (h : (IsKFlat X.O S.X₁ ∧ IsKFlat X.O S.X₂) ∨ (IsKFlat X.O S.X₁ ∧ IsKFlat X.O S.X₃) ∨
      (IsKFlat X.O S.X₂ ∧ IsKFlat X.O S.X₃)) :
    IsKFlat X.O S.X₁ ∧ IsKFlat X.O S.X₂ ∧ IsKFlat X.O S.X₃ := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₃⟩ | ⟨h₂, h₃⟩
  · exact ⟨h₁, h₂, isKFlat_X₃ X S hS hflat h₁ h₂⟩
  · exact ⟨h₁, isKFlat_X₂ X S hS hflat h₁ h₃, h₃⟩
  · exact ⟨isKFlat_X₁ X S hS hflat h₂ h₃, h₂, h₃⟩

end TwoOutOfThree

end Stacks.SheafOfModules

end
