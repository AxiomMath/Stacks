module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.LocallyQuasiIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.SheafifiedCechIndependence
import StacksCore.Tactic.StacksAttribute

/-!
# The object of Tag 099E depends only on the ideal *sheaf* the family generates

`AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_forall_span_eq` of
`SheafifiedCechIndependence.lean` compares the objects of two families which span the same ideal
of **sections** over every object. Two finite families of global sections generating the same
ideal **sheaf** span the same ideal of sections only after passing to a covering
(`AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq`), which is strictly weaker: a section of
the ideal sheaf over an object is only locally a combination of the generators.

This file closes that gap. The comparison maps of the presheaves of Čech complexes exist
regardless of any spanning hypothesis; what the hypothesis is used for is that they are
quasi-isomorphisms, and *after sheafification that is a local condition*. So the covering of
[Stacks, Tag 099E]'s hint suffices, and the conclusion holds on the nose over the object one
started from, with no gluing and no descent:

**two finite families of global sections generating the same sheaf of ideals give isomorphic
objects in `D(𝒪)`, compatibly with the maps to `𝒪`.**

## Main results

* `Stacks.CechPresheaf.isIso_homologyMap_app_cechPresheafRestrict`: over an object where the two
  families span the same ideal of sections, the restriction map of the presheaves of Čech
  complexes induces an isomorphism on the sections of every homology presheaf.
* `AlgebraicGeometry.RingedSite.quasiIso_sheafifiedCechRestrict_of_exists_mem_sieve`: **the
  comparison of the objects of a family and of a subfamily is a quasi-isomorphism as soon as the
  two families span the same ideal of sections along the arrows of a covering sieve of every
  object.**
* `AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_exists_mem_sieve_span_eq`: the same
  local hypothesis suffices for the comparison of two arbitrary families.
* `AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_idealOfGlobalSections_eq`:
  **[Stacks, Tag 099E]'s independence of the chosen finite generating family**, for two finite
  families of global sections generating the same sheaf of ideals.

## Implementation notes

The homology of a complex of presheaves of modules is computed object by object, and
sheafification of presheaves of modules is exact; both facts are the statement that a functor
preserving homology turns the map of homology objects into the map of homology objects of the
image, which is
`CategoryTheory.HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap` of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/LocallyQuasiIso.lean`. A map of presheaves of
modules which is invertible over the arrows of a covering sieve of every object is locally
bijective, hence inverted by sheafification, which is the other half of that file.

The presheaf of Čech complexes is `ℕ`-indexed and then extended by zero to the `ℤ` indexing a
derived category needs, so the per-object input is `ℕ`-indexed while the hypothesis of the
sheafification lemma is about the `ℤ`-indexed complex. The two are matched degree by degree:
in a degree in the image of `ComplexShape.embeddingUpNat` by
`CategoryTheory.HomologicalComplex.isIso_map_homologyMap_extendMap_iff`, and outside it by
`CategoryTheory.HomologicalComplex.isIso_map_homologyMap_extendMap`, the extension by zero being
exact there.

The three spellings of the presheaf of rings are kept apart as
`StacksFrontier/RingTheory/Cech/PresheafComplex.lean` keeps them apart: the per-object statement is
proved in the `R ⋙ forget₂ CommRingCat RingCat` spelling of that file and the ringed-site
statement in the `(ringSheaf X).obj` spelling of `SheafifiedCech.lean`, and the two are joined by
`exact`, which unfolds `CategoryTheory.sheafCompose`, and never by `rw`, which does not.

## References

* [Stacks Project, Tag 099E](https://stacks.math.columbia.edu/tag/099E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.CechPresheaf

variable {C : Type u} [Category.{v} C] (R : Cᵒᵖ ⥤ CommRingCat.{u}) {r s : ℕ}
  (f : ∀ V : Cᵒᵖ, Fin r → R.obj V)
  (hf : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (i : Fin r), (R.map a).hom (f V i) = f W i)
  (g : ∀ V : Cᵒᵖ, Fin s → R.obj V)
  (hg : ∀ {V W : Cᵒᵖ} (a : V ⟶ W) (j : Fin s), (R.map a).hom (g V j) = g W j)
  (e : Fin r ↪o Fin s) (he : ∀ (V : Cᵒᵖ) (i : Fin r), g V (e i) = f V i)

/-- **Over an object where the two families span the same ideal of sections, the restriction map
of the presheaves of Čech complexes is a quasi-isomorphism of complexes of modules.** This is
`Stacks.CechPresheaf.quasiIso_cechRestrict` read through
`Stacks.CechPresheaf.evaluation_map_cechPresheafRestrictNat`. -/
theorem quasiIso_evaluation_map_cechPresheafRestrictNat (V : Cᵒᵖ)
    (hspan : Ideal.span (Set.range (g V)) = Ideal.span (Set.range (f V))) :
    QuasiIso (((PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat)
          V).mapHomologicalComplex (ComplexShape.up ℕ)).map
      (cechPresheafRestrictNat R f hf g hg e he)) := by
  rw [evaluation_map_cechPresheafRestrictNat]
  have : QuasiIso (Cech.cechRestrict (f V) (ModuleCat.of (R.obj V) (R.obj V)) (g V) e (he V)) :=
    quasiIso_cechRestrict (f V) (g V) e (he V) (ModuleCat.of (R.obj V) (R.obj V)) hspan
  infer_instance

/-- **Over an object where the two families span the same ideal of sections, the restriction map
of the `ℤ`-indexed presheaves of Čech complexes induces an isomorphism on the sections of each
homology presheaf.**

In a degree in the image of `ComplexShape.embeddingUpNat` this is the `ℕ`-indexed statement
above; outside that image the extension by zero is exact and there is nothing to check. -/
theorem isIso_homologyMap_app_cechPresheafRestrict (V : Cᵒᵖ)
    (hspan : Ideal.span (Set.range (g V)) = Ideal.span (Set.range (f V))) (n : ℤ) :
    IsIso ((HomologicalComplex.homologyMap (cechPresheafRestrict R f hf g hg e he) n).app V) := by
  by_cases hn : ∃ m : ℕ, ComplexShape.embeddingUpNat.f m = n
  · obtain ⟨m, hm⟩ := hn
    have := quasiIso_evaluation_map_cechPresheafRestrictNat R f hf g hg e he V hspan
    have hm' : IsIso ((PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) V).map
        (HomologicalComplex.homologyMap (cechPresheafRestrictNat R f hf g hg e he) m)) :=
      (HomologicalComplex.quasiIsoAt_map_iff_isIso_map_homologyMap _ _ m).1 inferInstance
    exact (HomologicalComplex.isIso_map_homologyMap_extendMap_iff
      (cechPresheafRestrictNat R f hf g hg e he) ComplexShape.embeddingUpNat
      (PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) V) hm).2 hm'
  · exact HomologicalComplex.isIso_map_homologyMap_extendMap
      (cechPresheafRestrictNat R f hf g hg e he) ComplexShape.embeddingUpNat
      (PresheafOfModules.evaluation (R ⋙ forget₂ CommRingCat RingCat) V) n
      fun m hm => hn ⟨m, hm⟩

end Stacks.CechPresheaf

namespace AlgebraicGeometry.RingedSite

section Local

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J AddCommGrpCat.{u}] {r s : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin s → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The comparison of the objects of a family and of a subfamily is a quasi-isomorphism as soon
as the two families span the same ideal of sections along every arrow of a covering sieve of
every object.**

Being a quasi-isomorphism is, for a sheafified map, a local condition: the comparison of the
presheaves of Čech complexes exists with no spanning hypothesis at all, and what the hypothesis
supplies is that its homology presheaves become isomorphic after sheafification. -/
theorem quasiIso_sheafifiedCechRestrict_of_exists_mem_sieve (e : Fin r ↪o Fin s)
    (he : ∀ i, g (e i) = f i)
    (hspan : ∀ V : X.C, ∃ S : Sieve V, S ∈ X.J V ∧ ∀ ⦃Y : X.C⦄ (a : Y ⟶ V), S a →
      Ideal.span (Set.range (restrictGlobalSections X g (op Y))) =
        Ideal.span (Set.range (restrictGlobalSections X f (op Y)))) :
    QuasiIso (sheafifiedCechRestrict X f g e he) :=
  PresheafOfModules.quasiIso_sheafification_map_of_exists_mem_sieve
    (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) (cechPresheafRestrict X f g e he)
    fun n V => by
      obtain ⟨S, hS, hsp⟩ := hspan V
      exact ⟨S, hS, fun {Y} a ha =>
        Stacks.CechPresheaf.isIso_homologyMap_app_cechPresheafRestrict X.O.obj
          (cechFamily X f) (cechFamily_map X f) (cechFamily X g) (cechFamily_map X g) e
          (cechFamily_order_embedding X f g e he) (op Y) (hsp a ha) n⟩

/-- A family and a larger family spanning the same ideal of sections locally have their objects
in `D(𝒪)` identified by the comparison map. -/
private theorem isIso_Q_map_sheafifiedCechRestrict_of_exists_mem_sieve {t u : ℕ}
    (a : Fin t → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (b : Fin u → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (e : Fin t ↪o Fin u) (he : ∀ i, b (e i) = a i)
    (hspan : ∀ V : X.C, ∃ S : Sieve V, S ∈ X.J V ∧ ∀ ⦃Y : X.C⦄ (c : Y ⟶ V), S c →
      Ideal.span (Set.range (restrictGlobalSections X b (op Y))) =
        Ideal.span (Set.range (restrictGlobalSections X a (op Y)))) :
    IsIso (DerivedCategory.Q.map (sheafifiedCechRestrict X a b e he)) := by
  have := quasiIso_sheafifiedCechRestrict_of_exists_mem_sieve X a b e he hspan
  rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
  infer_instance

/-- **The objects of [Stacks, Tag 099E] attached to two families which span the same ideal of
sections along every arrow of a covering sieve of every object are isomorphic in `D(𝒪)` over
`𝒪`.** This is
`AlgebraicGeometry.RingedSite.exists_iso_sheafifiedCech_of_forall_span_eq` with its hypothesis
weakened to a local one, by the same zig-zag through the concatenated family. -/
theorem exists_iso_sheafifiedCech_of_exists_mem_sieve_span_eq
    (hspan : ∀ V : X.C, ∃ S : Sieve V, S ∈ X.J V ∧ ∀ ⦃Y : X.C⦄ (a : Y ⟶ V), S a →
      Ideal.span (Set.range (restrictGlobalSections X f (op Y))) =
        Ideal.span (Set.range (restrictGlobalSections X g (op Y)))) :
    ∃ e : DerivedCategory.Q.obj (sheafifiedCech X f) ≅
        DerivedCategory.Q.obj (sheafifiedCech X g),
      e.hom ≫ DerivedCategory.Q.map (sheafifiedCechAugmentation X g) =
        DerivedCategory.Q.map (sheafifiedCechAugmentation X f) := by
  have hfh : ∀ i, Fin.append f g (Fin.castAddOrderEmb s i) = f i := fun i => Fin.append_left f g i
  have hgh : ∀ j, Fin.append f g (Fin.natAddOrderEmb r j) = g j := fun j => Fin.append_right f g j
  have hsf : ∀ V : X.C, ∃ S : Sieve V, S ∈ X.J V ∧ ∀ ⦃Y : X.C⦄ (a : Y ⟶ V), S a →
      Ideal.span (Set.range (restrictGlobalSections X (Fin.append f g) (op Y))) =
        Ideal.span (Set.range (restrictGlobalSections X f (op Y))) := fun V => by
    obtain ⟨S, hS, hsp⟩ := hspan V
    exact ⟨S, hS, fun {Y} a ha =>
      span_range_restrictGlobalSections_append X f g (op Y) (hsp a ha)⟩
  have hsg : ∀ V : X.C, ∃ S : Sieve V, S ∈ X.J V ∧ ∀ ⦃Y : X.C⦄ (a : Y ⟶ V), S a →
      Ideal.span (Set.range (restrictGlobalSections X (Fin.append f g) (op Y))) =
        Ideal.span (Set.range (restrictGlobalSections X g (op Y))) := fun V => by
    obtain ⟨S, hS, hsp⟩ := hspan V
    exact ⟨S, hS, fun {Y} a ha =>
      (span_range_restrictGlobalSections_append X f g (op Y) (hsp a ha)).trans (hsp a ha)⟩
  have hif := isIso_Q_map_sheafifiedCechRestrict_of_exists_mem_sieve X f (Fin.append f g)
    (Fin.castAddOrderEmb s) hfh hsf
  have hig := isIso_Q_map_sheafifiedCechRestrict_of_exists_mem_sieve X g (Fin.append f g)
    (Fin.natAddOrderEmb r) hgh hsg
  refine ⟨(asIso (DerivedCategory.Q.map
      (sheafifiedCechRestrict X f (Fin.append f g) (Fin.castAddOrderEmb s) hfh))).symm ≪≫
    asIso (DerivedCategory.Q.map
      (sheafifiedCechRestrict X g (Fin.append f g) (Fin.natAddOrderEmb r) hgh)), ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, Category.assoc, ← Functor.map_comp,
    sheafifiedCechRestrict_comp_augmentation,
    ← sheafifiedCechRestrict_comp_augmentation X f (Fin.append f g) (Fin.castAddOrderEmb s) hfh,
    Functor.map_comp, IsIso.inv_hom_id_assoc]

/-- **[Stacks, Tag 099E]'s independence of the chosen finite generating family.** Two finite
families of global sections of `𝒪` generating the *same sheaf of ideals* give isomorphic objects
of `D(𝒪)`, compatibly with their maps to `𝒪`.

No covering survives in the conclusion, and no gluing is performed: the covering of the tag's
hint — `AlgebraicGeometry.RingedSite.exists_mem_sieve_span_eq` — enters only to see that the
comparison maps of the presheaves of Čech complexes become quasi-isomorphisms after
sheafification, which is a local condition on a map that is already globally defined. -/
theorem exists_iso_sheafifiedCech_of_idealOfGlobalSections_eq
    (h : idealOfGlobalSections X f = idealOfGlobalSections X g) :
    ∃ e : DerivedCategory.Q.obj (sheafifiedCech X f) ≅
        DerivedCategory.Q.obj (sheafifiedCech X g),
      e.hom ≫ DerivedCategory.Q.map (sheafifiedCechAugmentation X g) =
        DerivedCategory.Q.map (sheafifiedCechAugmentation X f) :=
  exists_iso_sheafifiedCech_of_exists_mem_sieve_span_eq X f g
    (exists_mem_sieve_span_eq X f g h)

end Local

end AlgebraicGeometry.RingedSite

end
