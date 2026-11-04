module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Coproducts
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedColimits
public import StacksFrontier.Algebra.Homology.StupidTruncation
public import StacksFrontier.Algebra.Homology.DerivedCategory.StupidTruncationTriangle
public import StacksFrontier.Algebra.Homology.Embedding.StupidTrunc
public import StacksFrontier.CategoryTheory.Abelian.GrothendieckAxioms.CountableCoproducts

/-!
# Exact functors out of `D(A)` inverting a morphism of bounded above complexes

Let `A` be an abelian category in which colimits over `ℕ` exist and are exact and countable
direct sums are exact, and let `Φ : D(A) ⥤ 𝒟` be an exact functor of triangulated categories
which commutes with countable direct sums. This file proves the dévissage by which a statement
about `Φ` on unbounded complexes is reduced to a statement about single objects:

* `isIso_map_Q_map_colimMap`: if `τ : F ⟶ G` is a morphism of systems `ℕ ⥤ C(A)` of cochain
  complexes and `Φ` inverts every `Q τₙ`, then `Φ` inverts `Q (colim τ)`. The colimit is the
  derived colimit (Stacks 0949), whose defining triangle `Φ` preserves.
* `isIso_map_Q_map_of_isStrictlyLE`: if `f : K ⟶ L` is a morphism of bounded above complexes and
  `Φ` inverts `fⁱ` placed in degree `i` for every `i`, then `Φ` inverts `Q f`. A bounded above
  complex is the colimit of its stupid truncations, each of which is filtered by the distinguished
  triangles `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p]`.
* `isIso_map_singleFunctor_of_zero`: the hypothesis in a degree `i` follows from the one in
  degree `0`, the functors `Φ` and `single` commuting with the shift.

This is the argument by which the source reduces a statement about bounded above complexes to one
about their terms ("way-out"), stated for a morphism of complexes rather than for an object: no
compatibility of a transformation with the shift is needed, only that `Φ` is exact.

## References

* [Stacks Project, Tag 0949](https://stacks.math.columbia.edu/tag/0949)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex ComplexShape

namespace Stacks.DerivedCategory.TermwiseInvertibility

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
  [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A]
  {D : Type*} [Category D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [HasColimitsOfShape (Discrete ℕ) D]
  (Φ : DerivedCategory A ⥤ D) [Φ.CommShift ℤ] [Φ.IsTriangulated]
  [PreservesColimitsOfShape (Discrete ℕ) Φ]

/-- A functor inverts a morphism which is conjugate by isomorphisms to a morphism it inverts. -/
private theorem isIso_map_of_comp_eq {C E : Type*} [Category C] [Category E] (G : C ⥤ E)
    {X Y X' Y' : C} (e : X' ≅ X) (e' : Y' ≅ Y) (g : X' ⟶ Y') (f : X ⟶ Y)
    (hf : e.hom ≫ f = g ≫ e'.hom) (hg : IsIso (G.map g)) : IsIso (G.map f) := by
  have : f = e.inv ≫ g ≫ e'.hom := by rw [← hf, Iso.inv_hom_id_assoc]
  rw [this, Functor.map_comp, Functor.map_comp]
  infer_instance

section Colimit

variable (hA : HasExactCountableDirectSums A)
include hA

omit [HasDerivedCategory A] [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] hA in
/-- A functor preserving countable direct sums inverts a direct sum of morphisms it inverts. -/
theorem isIso_map_sigmaMap {E : Type*} [Category E] [HasColimitsOfShape (Discrete ℕ) E]
    (G : CochainComplex A ℤ ⥤ E) [PreservesColimitsOfShape (Discrete ℕ) G]
    {F F' : ℕ → CochainComplex A ℤ} [HasCoproduct F] [HasCoproduct F'] (τ : ∀ n, F n ⟶ F' n)
    (h : ∀ n, IsIso (G.map (τ n))) : IsIso (G.map (Limits.Sigma.map τ)) := by
  have e : G.map (Limits.Sigma.map τ) = inv (sigmaComparison G F) ≫
      Limits.Sigma.map (fun n => G.map (τ n)) ≫ sigmaComparison G F' := by
    rw [IsIso.eq_inv_comp]
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [ι_comp_sigmaComparison_assoc, ← G.map_comp, Limits.Sigma.ι_map, Limits.Sigma.ι_map_assoc,
      ι_comp_sigmaComparison, ← G.map_comp]
  rw [e]
  have : IsIso (Limits.Sigma.map fun n => G.map (τ n)) :=
    (Limits.Sigma.mapIso fun n => asIso (G.map (τ n))).isIso_hom
  infer_instance

/-- **`Φ` inverts the colimit of a morphism of systems of complexes it inverts termwise.** The
termwise colimit is the derived colimit (Stacks 0949): the short exact sequence
`0 ⟶ ⊕ Fₙ ⟶ ⊕ Fₙ ⟶ colim Fₙ ⟶ 0` is natural in the system, so `τ` induces a morphism of the
distinguished triangles it gives, which `Φ` preserves; on the two direct sums it is a direct sum
of morphisms `Φ` inverts. -/
theorem isIso_map_Q_map_colimMap {F G : ℕ ⥤ CochainComplex A ℤ} (τ : F ⟶ G)
    (h : ∀ n, IsIso (Φ.map (DerivedCategory.Q.map (τ.app n)))) :
    IsIso (Φ.map (DerivedCategory.Q.map (colim.map τ))) := by
  have : HasCountableCoproducts A := hA.hasCoproducts
  have := derivedCategory_Q_preservesCoproductsOfShape A hA ℕ
  have hexact : PreservesFiniteLimits (colim : (ℕ ⥤ CochainComplex A ℤ) ⥤ _) :=
    HasExactColimitsOfShape.preservesFiniteLimits
  obtain ⟨wF, hF⟩ := Stacks.CountableCoproducts.shortExact_oneSubShift_piMap hexact F
  obtain ⟨wG, hG⟩ := Stacks.CountableCoproducts.shortExact_oneSubShift_piMap hexact G
  let σ := Limits.Sigma.map (fun n => τ.app n)
  have c₁ : Stacks.CountableCoproducts.oneSubShift F ≫ σ =
      σ ≫ Stacks.CountableCoproducts.oneSubShift G := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, Stacks.CountableCoproducts.ι_oneSubShift, Limits.Sigma.ι_map_assoc,
      Stacks.CountableCoproducts.ι_oneSubShift, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.assoc, Limits.Sigma.ι_map, ← Category.assoc, ← Category.assoc,
      ← NatTrans.naturality, Category.assoc, Category.assoc, Limits.Sigma.ι_map]
  have c₂ : Stacks.CountableCoproducts.piMap F ≫ colim.map τ =
      σ ≫ Stacks.CountableCoproducts.piMap G := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, Stacks.CountableCoproducts.ι_piMap, Limits.Sigma.ι_map_assoc,
      Stacks.CountableCoproducts.ι_piMap]
    exact ι_colimMap τ n
  let m : ShortComplex.mk _ _ wF ⟶ ShortComplex.mk _ _ wG :=
    { τ₁ := σ, τ₂ := σ, τ₃ := colim.map τ, comm₁₂ := c₁.symm, comm₂₃ := c₂.symm }
  let T := DerivedCategory.triangleOfSES.map hF hG m
  have hσ : IsIso (Φ.map (DerivedCategory.Q.map σ)) :=
    isIso_map_sigmaMap (DerivedCategory.Q ⋙ Φ) (fun n => τ.app n) h
  exact Pretriangulated.isIso₃_of_isIso₁₂ (Φ.mapTriangle.map T)
    (Φ.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hF))
    (Φ.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished hG)) hσ hσ

/-- **`Φ` inverts the component at a sequential colimit of a transformation between functors
preserving sequential colimits, as soon as it inverts the components at the terms.** -/
theorem isIso_map_Q_map_app_colimit {A' : Type*} [Category A']
    {T₁ T₂ : A' ⥤ CochainComplex A ℤ} (η : T₁ ⟶ T₂) (D : ℕ ⥤ A') [HasColimit D]
    [PreservesColimit D T₁] [PreservesColimit D T₂]
    (h : ∀ n, IsIso (Φ.map (DerivedCategory.Q.map (η.app (D.obj n))))) :
    IsIso (Φ.map (DerivedCategory.Q.map (η.app (colimit D)))) := by
  have hc := isIso_map_Q_map_colimMap Φ hA (Functor.whiskerLeft D η) h
  refine isIso_map_of_comp_eq (DerivedCategory.Q ⋙ Φ) (preservesColimitIso T₁ D).symm
    (preservesColimitIso T₂ D).symm _ _ ?_ hc
  refine colimit.hom_ext fun n => ?_
  rw [Iso.symm_hom, Iso.symm_hom, ι_preservesColimitIso_inv_assoc, colim_map, ι_colimMap_assoc,
    Functor.whiskerLeft_app, ι_preservesColimitIso_inv, NatTrans.naturality]

end Colimit

section Shift

omit [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] [HasColimitsOfShape (Discrete ℕ) D]
  [PreservesColimitsOfShape (Discrete ℕ) Φ] [HasZeroObject D]
  [∀ (n : ℤ), (shiftFunctor D n).Additive] [Pretriangulated D] [Φ.IsTriangulated]
  [Preadditive D] in
/-- Inverting the image of a morphism placed in degree `i` is the same as inverting it placed in
degree `0`: the two differ by a shift, with which `Φ` commutes. -/
theorem isIso_map_singleFunctor_iff {X Y : A} (g : X ⟶ Y) (i : ℤ) :
    IsIso (Φ.map ((DerivedCategory.singleFunctor A i).map g)) ↔
      IsIso (Φ.map ((DerivedCategory.singleFunctor A 0).map g)) := by
  let e : DerivedCategory.singleFunctor A 0 ⋙ shiftFunctor _ (-i) ≅
      DerivedCategory.singleFunctor A i :=
    (DerivedCategory.singleFunctors A).shiftIso (-i) i 0 (by omega)
  have h₁ : IsIso (Φ.map ((DerivedCategory.singleFunctor A i).map g)) ↔
      IsIso (Φ.map (((DerivedCategory.singleFunctor A 0).map g)⟦-i⟧')) :=
    (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
      (Φ.mapArrow.mapIso (Arrow.isoOfNatIso e (Arrow.mk g)).symm)
  have h₂ : IsIso (Φ.map (((DerivedCategory.singleFunctor A 0).map g)⟦-i⟧')) ↔
      IsIso ((Φ.map ((DerivedCategory.singleFunctor A 0).map g))⟦-i⟧') :=
    (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
      (Arrow.isoOfNatIso (Φ.commShiftIso (-i))
        (Arrow.mk ((DerivedCategory.singleFunctor A 0).map g)))
  rw [h₁, h₂]
  exact ⟨fun _ => isIso_of_reflects_iso _ (shiftFunctor D (-i)), fun _ => inferInstance⟩

end Shift

section Bounded

/-- A cocone on a sequential diagram whose legs are eventually isomorphisms is a colimit. -/
def isColimitOfEventuallyIsIso {C : Type*} [Category C] {E : ℕ ⥤ C} (c : Cocone E)
    (N : ℕ) (hN : ∀ n, N ≤ n → IsIso (c.ι.app n)) : IsColimit c := by
  letI := hN N le_rfl
  refine ⟨fun s => inv (c.ι.app N) ≫ s.ι.app N, ?_, ?_⟩
  · intro s n
    let k := max n N
    have := hN k (le_max_right _ _)
    have h : inv (c.ι.app N) ≫ s.ι.app N = inv (c.ι.app k) ≫ s.ι.app k := by
      apply (cancel_epi (c.ι.app N)).1
      rw [IsIso.hom_inv_id_assoc, ← c.w (homOfLE (le_max_right n N))]
      dsimp [k]
      simp only [Category.assoc, IsIso.hom_inv_id_assoc, s.w]
    rw [h, ← c.w (homOfLE (le_max_left n N))]
    dsimp [k]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, s.w]
  · intro s f hf
    apply (cancel_epi (c.ι.app N)).1
    simpa using hf N

open StacksDraft.StupidTruncation

variable {K L : CochainComplex A ℤ} (f : K ⟶ L)

omit [HasDerivedCategory A] [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] in
/-- The comparisons `σ^{≥b}K ⟶ σ^{≥a}K` are natural in the complex. -/
@[reassoc]
lemma stupidTruncMap_stupidTruncGEMapLE {a b : ℤ} (h : a ≤ b) :
    stupidTruncMap f (embeddingUpIntGE b) ≫ stupidTruncGEMapLE L h =
      stupidTruncGEMapLE K h ≫ stupidTruncMap f (embeddingUpIntGE a) := by
  have := mono_ιStupidTrunc L (embeddingUpIntGE a)
  refine (cancel_mono (ιStupidTrunc L (embeddingUpIntGE a))).1 ?_
  simp only [Category.assoc, stupidTruncGEMapLE_ι, stupidTruncMap_ιStupidTrunc]
  rw [← Category.assoc (stupidTruncGEMapLE K h), stupidTruncGEMapLE_ι]

omit [HasDerivedCategory A] [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] in
/-- The projections `σ^{≥p}K ⟶ Kᵖ[-p]` are natural in the complex. -/
@[reassoc]
lemma stupidTruncMap_stupidTruncGEπ (p : ℤ) :
    stupidTruncMap f (embeddingUpIntGE p) ≫ stupidTruncGEπ L p =
      stupidTruncGEπ K p ≫ (single A (.up ℤ) p).map (f.f p) := by
  apply to_single_hom_ext
  simp only [comp_f, stupidTruncGEπ_f, single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc,
    stupidTruncMap_stupidTruncXIso_hom_assoc]

/-- The morphism of filtration short exact sequences induced by `f`. -/
def stupidTruncGEShortComplexMap (p : ℤ) :
    stupidTruncGEShortComplex K p ⟶ stupidTruncGEShortComplex L p where
  τ₁ := stupidTruncMap f (embeddingUpIntGE (p + 1))
  τ₂ := stupidTruncMap f (embeddingUpIntGE p)
  τ₃ := (single A (.up ℤ) p).map (f.f p)
  comm₁₂ := stupidTruncMap_stupidTruncGEMapLE f (show p ≤ p + 1 by omega)
  comm₂₃ := stupidTruncMap_stupidTruncGEπ f p

/-- The tower of stupid truncations `σ^{≥ b + 1 - m}K`, indexed by `ℕ`. -/
def truncTower (K : CochainComplex A ℤ) (b : ℤ) : ℕ ⥤ CochainComplex A ℤ :=
  Monotone.functor (f := fun m : ℕ => (m : ℤ) - (b + 1))
      (fun _ _ h => by simpa using Int.ofNat_le.2 h) ⋙ stupidTruncTower K

/-- The morphism of towers of stupid truncations induced by `f`. -/
def truncTowerMap (b : ℤ) : truncTower K b ⟶ truncTower L b where
  app m := stupidTruncMap f (embeddingUpIntGE (-((m : ℤ) - (b + 1))))
  naturality m m' g := (stupidTruncMap_stupidTruncGEMapLE f
    (show -((m' : ℤ) - (b + 1)) ≤ -((m : ℤ) - (b + 1)) by have := leOfHom g; omega)).symm

/-- The cocone on `truncTower K b` with vertex `K`, given by the inclusions. -/
def truncTowerCocone (K : CochainComplex A ℤ) (b : ℤ) : Cocone (truncTower K b) where
  pt := K
  ι :=
    { app := fun m => ιStupidTrunc K (embeddingUpIntGE (-((m : ℤ) - (b + 1))))
      naturality := fun m m' g =>
        (stupidTruncGEMapLE_ι K (show -((m' : ℤ) - (b + 1)) ≤ -((m : ℤ) - (b + 1)) by
          have := leOfHom g; omega)).trans (Category.comp_id _).symm }

/-- A complex is the colimit of its stupid truncations from below: in each degree the tower is
eventually constant with value the term of the complex. -/
def isColimitTruncTowerCocone (K : CochainComplex A ℤ) (b : ℤ) :
    IsColimit (truncTowerCocone K b) := by
  refine HomologicalComplex.isColimitOfEval _ _ (fun n => ?_)
  have key : ∀ m : ℕ, (b + 1 - n).toNat ≤ m →
      IsIso (((truncTowerCocone K b).ι.app m).f n) := fun m hm => by
    change IsIso ((ιStupidTrunc K (embeddingUpIntGE (-((m : ℤ) - (b + 1))))).f n)
    rw [ιStupidTruncGE_f K _ n (by omega)]
    infer_instance
  exact isColimitOfEventuallyIsIso _ _ key

omit [HasDerivedCategory A] [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] in
/-- A complex strictly bounded above by `b` has vanishing stupid truncations beyond `b`. -/
lemma isZero_stupidTrunc_of_lt {b : ℤ} (M : CochainComplex A ℤ) [M.IsStrictlyLE b] (a : ℤ)
    (ha : b < a) : IsZero (M.stupidTrunc (embeddingUpIntGE a)) := by
  rw [IsZero.iff_id_eq_zero]
  ext n
  refine IsZero.eq_of_src ?_ _ _
  by_cases hn : a ≤ n
  · exact (CochainComplex.isZero_of_isStrictlyLE M b n (by omega)).of_iso
      (stupidTruncGEXIso M _ n hn)
  · exact CochainComplex.isZero_of_isStrictlyGE _ a n (by omega)

variable {b : ℤ} [K.IsStrictlyLE b] [L.IsStrictlyLE b]
  (h : ∀ i, IsIso (Φ.map ((DerivedCategory.singleFunctor A i).map (f.f i))))
include h

omit [HasColimitsOfShape (Discrete ℕ) D] [PreservesColimitsOfShape (Discrete ℕ) Φ]
  [HasColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ A] in
/-- `Φ` inverts every stupid truncation of `f`, by descending induction on the cut along the
triangles `σ^{≥p+1}K ⟶ σ^{≥p}K ⟶ Kᵖ[-p]`. -/
theorem isIso_map_Q_map_stupidTruncMap (k : ℕ) :
    IsIso (Φ.map (DerivedCategory.Q.map (stupidTruncMap f (embeddingUpIntGE (b + 1 - k))))) := by
  induction k with
  | zero =>
    exact IsZero.isIso
      (Φ.map_isZero (DerivedCategory.Q.map_isZero
        (isZero_stupidTrunc_of_lt (b := b) K _ (by omega))))
      (Φ.map_isZero (DerivedCategory.Q.map_isZero
        (isZero_stupidTrunc_of_lt (b := b) L _ (by omega)))) _
  | succ k ih =>
    set p : ℤ := b + 1 - ((k + 1 : ℕ) : ℤ) with hp
    have hp1 : b + 1 - (k : ℤ) = p + 1 := by omega
    rw [hp1] at ih
    let T := DerivedCategory.triangleOfSES.map (stupidTruncGEShortComplex_shortExact K p)
      (stupidTruncGEShortComplex_shortExact L p) (stupidTruncGEShortComplexMap f p)
    have h₃ : IsIso (Φ.map T.hom₃) := by
      refine isIso_map_of_comp_eq Φ ((DerivedCategory.singleFunctorIsoCompQ A p).app (K.X p))
        ((DerivedCategory.singleFunctorIsoCompQ A p).app (L.X p)) _ _ ?_ (h p)
      exact ((DerivedCategory.singleFunctorIsoCompQ A p).hom.naturality (f.f p)).symm
    exact Pretriangulated.isIso₂_of_isIso₁₃ (Φ.mapTriangle.map T)
      (Φ.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished _))
      (Φ.map_distinguished _ (DerivedCategory.triangleOfSES_distinguished _)) ih h₃

include b in
/-- **`Φ` inverts a morphism of bounded above complexes which it inverts termwise**: if `Φ`
inverts `fⁱ` placed in degree `i` for every `i`, then it inverts `Q f`. -/
theorem isIso_map_Q_map_of_isStrictlyLE (hA : HasExactCountableDirectSums A) :
    IsIso (Φ.map (DerivedCategory.Q.map f)) := by
  have hτ := isIso_map_Q_map_colimMap Φ hA (truncTowerMap f b) (fun m => by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, -((m : ℤ) - (b + 1)) = b + 1 - k := ⟨m, by ring⟩
    show IsIso (Φ.map (DerivedCategory.Q.map
      (stupidTruncMap f (embeddingUpIntGE (-((m : ℤ) - (b + 1)))))))
    rw [hk]
    exact isIso_map_Q_map_stupidTruncMap Φ f h k)
  refine isIso_map_of_comp_eq (DerivedCategory.Q ⋙ Φ)
    (colimit.isoColimitCocone ⟨_, isColimitTruncTowerCocone K b⟩)
    (colimit.isoColimitCocone ⟨_, isColimitTruncTowerCocone L b⟩) _ _ ?_ hτ
  refine colimit.hom_ext fun m => ?_
  rw [colim_map, ι_colimMap_assoc, colimit.isoColimitCocone_ι_hom]
  erw [colimit.isoColimitCocone_ι_hom_assoc]
  exact (stupidTruncMap_ιStupidTrunc (embeddingUpIntGE (-((m : ℤ) - (b + 1)))) f).symm

end Bounded

end Stacks.DerivedCategory.TermwiseInvertibility
