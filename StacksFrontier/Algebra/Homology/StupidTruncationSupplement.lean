module

public import StacksFrontier.Algebra.Homology.StupidTruncation

/-!
# Functoriality of the stupid truncation along an additive functor

For an additive functor `Φ` and a map of complexes `κ : Φ K ⟶ L`, the induced maps
`Φ(σ^{≥a}K) ⟶ σ^{≥a}L` and the induced morphism from `Φ` of the short complex
`σ^{≥a+1}K ⟶ σ^{≥a}K ⟶ (single a).obj (Kᵃ)` to the short complex of `L`.

## Main definitions

* `StacksDraft.StupidTruncation.isIso_ιStupidTrunc`: the inclusion of the stupid truncation of a
  complex already strictly supported on the embedding is an isomorphism.
* `StacksDraft.StupidTruncation.stupidTruncGEMapOfHom`: the map `Φ(σ^{≥a}K) ⟶ σ^{≥a}L`.
* `StacksDraft.StupidTruncation.stupidTruncGEShortComplexMapOfHom`: the morphism of short
  complexes it induces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.StupidTruncation

section Inclusion

open HomologicalComplex ComplexShape

variable {A : Type*} [Category* A] [HasZeroMorphisms A] [HasZeroObject A]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (K : HomologicalComplex A c') (e : c.Embedding c')

/-- The inclusion of the stupid truncation of a complex which is already strictly supported on
`e` is an isomorphism. -/
instance isIso_ιStupidTrunc [e.IsTruncGE] [K.IsStrictlySupported e] : IsIso (ιStupidTrunc K e) := by
  have : ∀ i', IsIso ((ιStupidTrunc K e).f i') := fun i' => by
    by_cases hi' : ∃ i, e.f i = i'
    · obtain ⟨i, hi⟩ := hi'
      exact isIso_ιStupidTrunc_f K e hi
    · exact IsZero.isIso (K.isZero_stupidTrunc_X e i' (by simpa using hi'))
        (K.isZero_X_of_isStrictlySupported e i' (by simpa using hi')) _
  exact HomologicalComplex.Hom.isIso_of_components _

end Inclusion

attribute [local instance] mono_ιStupidTrunc

section Functoriality

open HomologicalComplex ComplexShape

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [HasZeroObject C]
  [Preadditive D] [HasZeroObject D] (Φ : C ⥤ D) [Φ.Additive]
  {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}

/-- The map `Φ(σ^{≥a}K) ⟶ σ^{≥a}L` induced by a map of complexes `κ : Φ K ⟶ L`: the image under
`Φ` of the truncation is strictly supported in degrees `≥ a`, so its composite with `κ` factors
through `σ^{≥a}L`. -/
noncomputable def stupidTruncGEMapOfHom (κ : (Φ.mapHomologicalComplex _).obj K ⟶ L) (a : ℤ) :
    (Φ.mapHomologicalComplex _).obj (K.stupidTrunc (embeddingUpIntGE a)) ⟶
      L.stupidTrunc (embeddingUpIntGE a) :=
  liftStupidTrunc L (embeddingUpIntGE a)
    ((Φ.mapHomologicalComplex _).map (ιStupidTrunc K (embeddingUpIntGE a)) ≫ κ)

/-- The composite of `stupidTruncGEMapOfHom Φ κ a` with the inclusion `σ^{≥a}L ⟶ L` is `Φ` of the
inclusion `σ^{≥a}K ⟶ K` followed by `κ`. -/
@[reassoc (attr := simp)]
lemma stupidTruncGEMapOfHom_ι (κ : (Φ.mapHomologicalComplex _).obj K ⟶ L) (a : ℤ) :
    stupidTruncGEMapOfHom Φ κ a ≫ ιStupidTrunc L (embeddingUpIntGE a) =
      (Φ.mapHomologicalComplex _).map (ιStupidTrunc K (embeddingUpIntGE a)) ≫ κ :=
  liftStupidTrunc_ι _ _ _

/-- In a retained degree, the induced map of truncations is `κ` read through the identifications
of terms. -/
lemma stupidTruncGEMapOfHom_f (κ : (Φ.mapHomologicalComplex _).obj K ⟶ L) (a m : ℤ)
    (h : a ≤ m) :
    (stupidTruncGEMapOfHom Φ κ a).f m = Φ.map (stupidTruncGEXIso K a m h).hom ≫ κ.f m ≫
      (stupidTruncGEXIso L a m h).inv := by
  have e := congrArg (fun f => f.f m) (stupidTruncGEMapOfHom_ι Φ κ a)
  simp only [HomologicalComplex.comp_f, ιStupidTruncGE_f _ a m h,
    Functor.mapHomologicalComplex_map_f] at e
  rw [← Category.assoc, ← e, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A map into a stupid truncation is determined by its composite with the inclusion. -/
lemma stupidTrunc_hom_ext {M : CochainComplex C ℤ} {a : ℤ}
    {f g : M ⟶ K.stupidTrunc (embeddingUpIntGE a)}
    (h : f ≫ ιStupidTrunc K (embeddingUpIntGE a) = g ≫ ιStupidTrunc K (embeddingUpIntGE a)) :
    f = g :=
  (cancel_mono _).1 h

end Functoriality

section FunctorialityShortExact

open HomologicalComplex ComplexShape

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D] (Φ : C ⥤ D)
  [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  {K : CochainComplex C ℤ} {L : CochainComplex D ℤ}

/-- **The morphism of short complexes induced by a map of complexes.** For `κ : Φ K ⟶ L`, the
morphism from `Φ` of `σ^{≥a+1}K ⟶ σ^{≥a}K ⟶ (single a).obj (Kᵃ)` to
`σ^{≥a+1}L ⟶ σ^{≥a}L ⟶ (single a).obj (Lᵃ)`. -/
noncomputable def stupidTruncGEShortComplexMapOfHom (κ : (Φ.mapHomologicalComplex _).obj K ⟶ L)
    (a : ℤ) :
    (stupidTruncGEShortComplex K a).map (Φ.mapHomologicalComplex _) ⟶
      stupidTruncGEShortComplex L a where
  τ₁ := stupidTruncGEMapOfHom Φ κ (a + 1)
  τ₂ := stupidTruncGEMapOfHom Φ κ a
  τ₃ := (Φ.mapCochainComplexSingleFunctor a).hom.app (K.X a) ≫
    (single D (ComplexShape.up ℤ) a).map (κ.f a)
  comm₁₂ := by
    apply stupidTrunc_hom_ext
    simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f,
      stupidTruncGEShortComplex, Category.assoc, stupidTruncGEMapLE_ι, stupidTruncGEMapOfHom_ι,
      ← Functor.map_comp_assoc, stupidTruncGEMapOfHom_ι_assoc]
  comm₂₃ := by
    apply to_single_hom_ext
    have h := congrArg (fun f => f.f a) (stupidTruncGEMapOfHom_ι Φ κ a)
    simp only [HomologicalComplex.comp_f, ιStupidTruncGE_f _ a a le_rfl,
      Functor.mapHomologicalComplex_map_f] at h
    simp only [ShortComplex.map_X₂, ShortComplex.map_X₃, ShortComplex.map_g,
      stupidTruncGEShortComplex, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      stupidTruncGEπ_f, Functor.map_comp, Category.assoc, Functor.mapCochainComplexSingleFunctor,
      singleMapHomologicalComplex_hom_app_self, single_map_f_self, ← reassoc_of% h]
    simpa using h

end FunctorialityShortExact

end StacksDraft.StupidTruncation
