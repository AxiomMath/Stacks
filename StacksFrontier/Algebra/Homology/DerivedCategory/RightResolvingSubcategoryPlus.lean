module

public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bounded below derived categories through a right resolving exact functor

Let `F : C ⥤ D` be an exact fully faithful functor between abelian categories such that every
object of `D` is a subobject of an object in the image of `F`. Then `D⁺(D)` is the localization
of `K⁺(C)` at the morphisms that `K⁺(F)` turns into quasi-isomorphisms.

## Main results

* `CategoryTheory.LocalizerMorphism.hasLeftCalculusOfFractions_of_hasRightResolutions` — a
  fully faithful induced localizer morphism with right resolutions transports a left calculus
  of fractions back to its source.
* `CategoryTheory.LocalizerMorphism.isLocalizedEquivalence_of_hasRightResolutions` — such a
  localizer morphism is a localized equivalence.
* `CategoryTheory.Functor.isLocalization_mapHomotopyCategoryPlus_comp`,
  `CategoryTheory.Functor.isLocalization_mapHomotopyCategoryPlus_comp'` and
  `CategoryTheory.Functor.isLocalization_mapHomotopyCategoryPlus_comp_Qh` — the functor
  `K⁺(C) ⥤ D⁺(D)` is a localization functor at the inverse image of the quasi-isomorphisms.

## Implementation notes

The right resolutions of a bounded below complex come from
`CochainComplex.exists_quasiIso_prop_isStrictlyGE` applied to the essential image of `F`, whose
terms are then lifted back along `F` term by term.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe v₁ v₂ v₃ u₁ u₂ u₃ w

namespace CategoryTheory

namespace LocalizerMorphism

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {W₁ : MorphismProperty C} {W₂ : MorphismProperty D}

/-- A fully faithful localizer morphism which induces its source class and has right
resolutions pulls a left calculus of fractions back from its target. -/
public theorem hasLeftCalculusOfFractions_of_hasRightResolutions
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsInduced]
    [Φ.functor.Full] [Φ.functor.Faithful]
    [W₂.HasLeftCalculusOfFractions] [Φ.HasRightResolutions] :
    W₁.HasLeftCalculusOfFractions := by
  have : W₁.IsMultiplicative := by
    rw [← Φ.inverseImage_eq]
    infer_instance
  have hiff : ∀ {X Y : C} (h : X ⟶ Y), W₂ (Φ.functor.map h) ↔ W₁ h := by
    intro X Y h
    have heq := congrArg (fun W : MorphismProperty C => W h) Φ.inverseImage_eq
    exact Iff.of_eq (by simpa only [MorphismProperty.inverseImage_iff] using heq)
  have hsat : ∀ {X Y : C} (h : X ⟶ Y), W₂ (Φ.functor.map h) → W₁ h := fun h hh => (hiff h).mp hh
  constructor
  · intro X Y φ
    have hφs : W₂ (Φ.functor.map φ.s) := (hiff φ.s).mpr φ.hs
    let φ' : W₂.RightFraction (Φ.functor.obj X) (Φ.functor.obj Y) :=
      ⟨Φ.functor.map φ.s, hφs, Φ.functor.map φ.f⟩
    obtain ⟨ψ, hψ⟩ := MorphismProperty.HasLeftCalculusOfFractions.exists_leftFraction φ'
    let ρ : Φ.RightResolution ψ.Y' := Classical.arbitrary _
    let f := Φ.functor.preimage (ψ.f ≫ ρ.w)
    let s := Φ.functor.preimage (ψ.s ≫ ρ.w)
    have hs : W₁ s := hsat s (by
      rw [Functor.map_preimage]
      exact W₂.comp_mem _ _ ψ.hs ρ.hw)
    refine ⟨⟨f, s, hs⟩, ?_⟩
    apply Φ.functor.map_injective
    change Φ.functor.map φ.f ≫ ψ.s = Φ.functor.map φ.s ≫ ψ.f at hψ
    simpa only [Functor.map_comp, f, s, Functor.map_preimage, Category.assoc] using
      congrArg (fun q => q ≫ ρ.w) hψ
  · intro X' X Y f g s hs h
    obtain ⟨Z, t, ht, hfg⟩ := MorphismProperty.HasLeftCalculusOfFractions.ext
      (Φ.functor.map f) (Φ.functor.map g) (Φ.functor.map s) ((hiff s).mpr hs)
      (by simpa using congrArg (fun q => Φ.functor.map q) h)
    let ρ : Φ.RightResolution Z := Classical.arbitrary _
    let t' := Φ.functor.preimage (t ≫ ρ.w)
    have ht' : W₁ t' := hsat t' (by
      rw [Functor.map_preimage]
      exact W₂.comp_mem _ _ ht ρ.hw)
    refine ⟨ρ.X₁, t', ht', ?_⟩
    apply Φ.functor.map_injective
    simpa [t', ← Category.assoc] using congrArg (fun q => q ≫ ρ.w) hfg

/-- A fully faithful localizer morphism which induces its source class and has right
resolutions is a localized equivalence: the induced functor between the localizations is
essentially surjective by the resolutions and fully faithful by the calculus of fractions. -/
@[sga "4½ Etat_0 4.2.3" "more general"]
public theorem isLocalizedEquivalence_of_hasRightResolutions
    (Φ : LocalizerMorphism W₁ W₂) [Φ.IsInduced]
    [Φ.functor.Full] [Φ.functor.Faithful]
    [W₁.HasLeftCalculusOfFractions] [W₂.HasLeftCalculusOfFractions]
    [Φ.HasRightResolutions] : Φ.IsLocalizedEquivalence := by
  let L₁ := W₁.Q
  let L₂ := W₂.Q
  let G := Φ.localizedFunctor L₁ L₂
  have e : Φ.functor ⋙ L₂ ≅ L₁ ⋙ G := CatCommSq.iso Φ.functor L₁ L₂ G
  have N : ∀ {X Y : C} (h : X ⟶ Y),
      e.hom.app X ≫ G.map (L₁.map h) = L₂.map (Φ.functor.map h) ≫ e.hom.app Y :=
    fun h ↦ (e.hom.naturality h).symm
  have hsat : ∀ {X Y : C} (h : X ⟶ Y), W₂ (Φ.functor.map h) → W₁ h := by
    intro X Y h hh
    rw [← Φ.inverseImage_eq]
    exact hh
  have : L₁.EssSurj := Localization.essSurj L₁ W₁
  have : G.EssSurj := by
    refine ⟨fun Y ↦ ?_⟩
    obtain ⟨X, ⟨i⟩⟩ := (Φ.essSurj_of_hasRightResolutions L₂).mem_essImage Y
    exact ⟨L₁.obj X, ⟨(e.app X).symm ≪≫ i⟩⟩
  have : G.Full := by
    refine G.full_of_comp_essSurj L₁ (fun X Y φ ↦ ?_)
    obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction L₂ W₂ (e.hom.app X ≫ φ ≫ e.inv.app Y)
    let ρ : Φ.RightResolution ψ.Y' := Classical.arbitrary _
    let g : W₁.LeftFraction X Y :=
      { Y' := ρ.X₁
        f := Φ.functor.preimage (ψ.f ≫ ρ.w)
        s := Φ.functor.preimage (ψ.s ≫ ρ.w)
        hs := hsat _ (by simpa using W₂.comp_mem _ _ ψ.hs ρ.hw) }
    have hφ : e.hom.app X ≫ φ = ψ.map L₂ (Localization.inverts _ _) ≫ e.hom.app Y := by
      rw [← hψ]
      simp
    refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
    have := Localization.inverts L₁ W₁ _ g.hs
    rw [← cancel_mono (G.map (L₁.map g.s)), ← G.map_comp,
      MorphismProperty.LeftFraction.map_comp_map_s,
      ← cancel_epi (e.hom.app X), N, ← Category.assoc, hφ,
      Category.assoc, N, ← Category.assoc]
    congr 1
    simp [g]
  have : G.Faithful := by
    refine Functor.faithful_of_comp_of_hasLeftCalculusOfFractions L₁ W₁ G
      (fun X Y f g hfg ↦ ?_)
    have h₂ : L₂.map (Φ.functor.map f) = L₂.map (Φ.functor.map g) := by
      rw [← cancel_mono (e.hom.app Y), ← N, ← N, hfg]
    rw [MorphismProperty.map_eq_iff_postcomp L₂ W₂] at h₂
    obtain ⟨Z, s, hsW, fac⟩ := h₂
    let ρ : Φ.RightResolution Z := Classical.arbitrary _
    let t : Y ⟶ ρ.X₁ := Φ.functor.preimage (s ≫ ρ.w)
    have ht : W₁ t := hsat _ (by simpa [t] using W₂.comp_mem _ _ hsW ρ.hw)
    have := Localization.inverts L₁ W₁ _ ht
    rw [← cancel_mono (L₁.map t), ← L₁.map_comp, ← L₁.map_comp]
    congr 1
    apply Φ.functor.map_injective
    simp [t, ← Category.assoc, fac]
  have : G.IsEquivalence := { }
  exact LocalizerMorphism.IsLocalizedEquivalence.mk' Φ L₁ L₂ G

end LocalizerMorphism

end CategoryTheory

namespace CochainComplex

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]

/-- A cochain complex all of whose terms lie in the essential image of a fully faithful
additive functor is the image of a cochain complex of the source. -/
public theorem exists_iso_mapHomologicalComplex_of_forall_essImage
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful] (K : CochainComplex D ℤ)
    (hK : ∀ n, ∃ X : C, Nonempty (F.obj X ≅ K.X n)) :
    ∃ L : CochainComplex C ℤ,
      Nonempty ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ K) := by
  choose X e using hK
  let e' (n : ℤ) : F.obj (X n) ≅ K.X n := Classical.choice (e n)
  let d (n : ℤ) : X n ⟶ X (n + 1) :=
    F.preimage ((e' n).hom ≫ K.d n (n + 1) ≫ (e' (n + 1)).inv)
  have hdd (n : ℤ) : d n ≫ d (n + 1) = 0 := by
    apply F.map_injective
    simp only [Functor.map_comp, F.map_zero]
    dsimp [d, e']
    rw [F.map_preimage, F.map_preimage]
    simp
  let L : CochainComplex C ℤ := CochainComplex.of X d hdd
  refine ⟨L, ⟨HomologicalComplex.Hom.isoOfComponents (fun i => e' i) (fun i j hij => ?_)⟩⟩
  obtain rfl : j = i + 1 := by simpa using hij.symm
  show (e' i).hom ≫ K.d i (i + 1) =
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).d i (i + 1) ≫ (e' (i + 1)).hom
  simp only [Functor.mapHomologicalComplex_obj_d, L, CochainComplex.of_d]
  simp [d, e']

end CochainComplex

namespace CategoryTheory.Functor

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [Abelian C] [Abelian D]

/-- If every object of `D` embeds into an object in the image of a fully faithful exact functor
`F : C ⥤ D`, then every bounded below complex over `D` admits a quasi-isomorphism to the image
of a bounded below complex over `C`. -/
public theorem exists_quasiIso_mapHomotopyCategoryPlus
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (hF : ∀ Y : D, ∃ (X : C) (i : Y ⟶ F.obj X), Mono i) (K : HomotopyCategory.Plus D) :
    ∃ (L : HomotopyCategory.Plus C) (r : K ⟶ F.mapHomotopyCategoryPlus.obj L),
      HomotopyCategory.Plus.quasiIso D r := by
  let P : ObjectProperty D := F.essImage
  have : P.ContainsZero := ⟨F.obj 0, F.map_isZero (isZero_zero C), F.obj_mem_essImage 0⟩
  have hP : ∀ Y : D, ∃ (Z : D) (_ : P Z) (i : Y ⟶ Z), Mono i := by
    intro Y
    obtain ⟨X, i, hi⟩ := hF Y
    exact ⟨F.obj X, F.obj_mem_essImage X, i, hi⟩
  obtain ⟨K, rfl⟩ := HomotopyCategory.Plus.quotient_obj_surjective K
  obtain ⟨a, ha⟩ := K.property
  obtain ⟨N, r, hr, hN, _, hn⟩ := CochainComplex.exists_quasiIso_prop_isStrictlyGE P hP a K.obj
  obtain ⟨L, ⟨e⟩⟩ := CochainComplex.exists_iso_mapHomologicalComplex_of_forall_essImage F N hN
  have hL : L.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    apply IsZero.of_full_of_faithful_of_isZero F
    exact ((HomologicalComplex.eval D (ComplexShape.up ℤ) i).mapIso e).isZero_iff.mpr
      (N.isZero_of_isStrictlyGE a i hi)
  let L' : CochainComplex.Plus C := ⟨L, a, hL⟩
  refine ⟨(HomotopyCategory.Plus.quotient C).obj L',
    ObjectProperty.homMk ((HomotopyCategory.quotient D _).map (r ≫ e.inv)), ?_⟩
  rw [HomotopyCategory.Plus.quasiIso_iff]
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
    (show QuasiIso (r ≫ e.inv) from inferInstance)

/-- **The bounded below derived category through a right resolving functor.** If `F : C ⥤ D` is
a fully faithful exact functor of abelian categories and every object of `D` embeds into an
object of the image of `F`, then the bounded below derived category of `D` — any localization
`L` of `K⁺(D)` at the quasi-isomorphisms — is the localization of `K⁺(C)` at the morphisms
whose image under `K⁺(F)` is a quasi-isomorphism. -/
public theorem isLocalization_mapHomotopyCategoryPlus_comp
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (hF : ∀ Y : D, ∃ (X : C) (i : Y ⟶ F.obj X), Mono i)
    {E : Type u₃} [Category.{v₃} E] (L : HomotopyCategory.Plus D ⥤ E)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso D)] :
    (F.mapHomotopyCategoryPlus ⋙ L).IsLocalization
      ((HomotopyCategory.Plus.quasiIso D).inverseImage F.mapHomotopyCategoryPlus) := by
  let W := HomotopyCategory.Plus.quasiIso D
  let Φ : LocalizerMorphism (W.inverseImage F.mapHomotopyCategoryPlus) W :=
    { functor := F.mapHomotopyCategoryPlus, map := fun _ _ _ h => h }
  have : Φ.IsInduced := ⟨rfl⟩
  have : Φ.functor.Full := inferInstanceAs F.mapHomotopyCategoryPlus.Full
  have : Φ.functor.Faithful := inferInstanceAs F.mapHomotopyCategoryPlus.Faithful
  have : Φ.HasRightResolutions := by
    intro K
    obtain ⟨L, r, hr⟩ := exists_quasiIso_mapHomotopyCategoryPlus F hF K
    exact ⟨{ X₁ := L, w := r, hw := hr }⟩
  have : W.HasLeftCalculusOfFractions := by
    dsimp [W]
    rw [HomotopyCategory.Plus.quasiIso_eq_subcategoryAcyclic_trW]
    infer_instance
  have : (W.inverseImage F.mapHomotopyCategoryPlus).HasLeftCalculusOfFractions :=
    LocalizerMorphism.hasLeftCalculusOfFractions_of_hasRightResolutions Φ
  have : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.isLocalizedEquivalence_of_hasRightResolutions Φ
  exact LocalizerMorphism.IsLocalizedEquivalence.isLocalization Φ L

/-- `CategoryTheory.Functor.isLocalization_mapHomotopyCategoryPlus_comp` for a class of
morphisms given together with its identification with the inverse image of the
quasi-isomorphisms. -/
public theorem isLocalization_mapHomotopyCategoryPlus_comp'
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (hF : ∀ Y : D, ∃ (X : C) (i : Y ⟶ F.obj X), Mono i)
    {E : Type u₃} [Category.{v₃} E] (L : HomotopyCategory.Plus D ⥤ E)
    [L.IsLocalization (HomotopyCategory.Plus.quasiIso D)]
    (W : MorphismProperty (HomotopyCategory.Plus C))
    (hW : W = (HomotopyCategory.Plus.quasiIso D).inverseImage F.mapHomotopyCategoryPlus) :
    (F.mapHomotopyCategoryPlus ⋙ L).IsLocalization W := by
  subst hW
  exact isLocalization_mapHomotopyCategoryPlus_comp F hF L

/-- **[Stacks, Tag 06ZR] in the abstract**, for Mathlib's model `D⁺(D)` of the bounded below
derived category: if `F : C ⥤ D` is a fully faithful exact functor of abelian categories and
every object of `D` embeds into an object of the image of `F`, then `D⁺(D)` is the localization
of `K⁺(C)` at the morphisms whose image under `K⁺(F)` is a quasi-isomorphism. -/
public theorem isLocalization_mapHomotopyCategoryPlus_comp_Qh [HasDerivedCategory.{w} D]
    (F : C ⥤ D) [F.Additive] [F.Full] [F.Faithful]
    (hF : ∀ Y : D, ∃ (X : C) (i : Y ⟶ F.obj X), Mono i) :
    (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).IsLocalization
      ((HomotopyCategory.Plus.quasiIso D).inverseImage F.mapHomotopyCategoryPlus) :=
  isLocalization_mapHomotopyCategoryPlus_comp F hF DerivedCategory.Plus.Qh

end CategoryTheory.Functor

end
