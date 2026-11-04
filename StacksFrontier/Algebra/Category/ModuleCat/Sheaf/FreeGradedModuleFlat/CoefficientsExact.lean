module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleCoefficients
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeGradedModuleTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullbackIdentity
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of `X ↦ X[S]`

## Main definitions

* `SheafOfModules.coeffPieceFunctor` is `X ↦ X[S]` in degree `n` as a functor on graded sheaves
  of modules.

## Main results

* `SheafOfModules.coeffPiece_shortExact`: the construction `X ↦ X[S]` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeGradedModuleCoefficients.lean` carries a
  degreewise short exact sequence of graded sheaves of modules to a short exact sequence in
  every degree.
* `SheafOfModules.coeffPiece_exact`: `X ↦ X[S]` preserves exactness, not merely short
  exactness.

## Implementation notes

Exactness of `X ↦ X[S]` is proved on the presentation and then sheafified. On the presentation it
is the exactness of a direct sum of sequences of modules, checked componentwise; sheafification
of presheaves of modules is exact, which disposes of the monomorphism and of exactness in the
middle. The epimorphism at the right-hand end cannot come from that, an epimorphism of sheaves
of modules being only locally surjective on sections: it is proved by right-cancellation, using
`SheafOfModules.coeffPiece_hom_ext` to reduce to the summands of the presentation and then
`Stacks.eq_of_forall_lift` with the local surjectivity that
`Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi` extracts from the epimorphism.

Acyclicity is exactness of short complexes which are *not* short exact, so short exactness has to
be upgraded to preservation of exactness. For an additive functor between abelian categories that
is `CategoryTheory.Functor.exact_tfae`, which needs `X ↦ X[S]` as a functor on an abelian
category of graded sheaves of modules. The abelian category used is the functor category
`Discrete ℤ ⥤ SheafOfModules R` and not the product `ℤ → SheafOfModules R`: Mathlib has
`CategoryTheory.functorCategoryAbelian` and nothing making a pi category abelian.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe w t a m z v u

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-! ### Sheafification of presheaves of modules, and sections of sheaves of modules

Three facts used below and stated for an arbitrary sheaf of rings: sheafification of presheaves
of modules is additive, a monomorphism of sheaves of modules is injective on sections, and a
short exact sequence of sheaves of modules is exact on sections except at its right-hand end. -/

section Sheafification

variable [HasWeakSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

/-- Sheafification of presheaves of modules is additive, being a left adjoint between
preadditive categories with biproducts. -/
instance sheafification_additive_of_ringSheaf :
    Functor.Additive (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{z} R.obj ⥤ SheafOfModules.{z} R) := by
  have h : PreservesBinaryBiproducts (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{z} R.obj ⥤ SheafOfModules.{z} R) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

end Sheafification

section Sections

variable [HasSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}]

omit [HasSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}] in
/-- A monomorphism of sheaves of modules is injective on sections: taking sections over an object
of the site is left exact. -/
theorem injective_of_mono_sections {M N : SheafOfModules.{z} R} (f : M ⟶ N) (hf : Mono f)
    (U : Cᵒᵖ) : Function.Injective (homSections f U) := by
  have : Mono ((SheafOfModules.forget.{z} R).map f) := inferInstance
  exact PresheafOfModules.injective_of_mono ((SheafOfModules.forget.{z} R).map f) U

/-- A short exact sequence of sheaves of modules is exact on sections in the middle: a section of
the middle term killed by the second map comes from the first. Taking sections is left exact,
which is what this uses, and no more is true — the second map need not be surjective on
sections. -/
theorem exists_of_shortExact_sections {T : ShortComplex (SheafOfModules.{z} R)}
    (hT : T.ShortExact) (U : Cᵒᵖ) (y : T.X₂.val.obj U) (hy : homSections T.g U y = 0) :
    ∃ x : T.X₁.val.obj U, homSections T.f U x = y := by
  have hF := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (F := SheafOfModules.forget.{z} R ⋙ PresheafOfModules.evaluation R.obj U)).mp
      inferInstance T hT
  exact (ShortComplex.moduleCat_exact_iff _).mp hF.1 y hy

end Sections

/-! ### Objectwise criteria in presheaves of modules

Taking sections over an object of the site is exact on presheaves of modules, so it computes
zero objects and homology. -/

section Objectwise

variable {R₀ : Cᵒᵖ ⥤ RingCat.{t}}

/-- The image of the homology of a short complex under an exact functor is a zero object if the
image of the short complex is exact. -/
private theorem isZero_obj_homology_of_exact_map {A B : Type*} [Category A] [Category B]
    [Preadditive A] [Preadditive B] (F : A ⥤ B) [F.Additive] [F.PreservesHomology]
    (T : ShortComplex A) [T.HasHomology] [(T.map F).HasHomology] (h : (T.map F).Exact) :
    IsZero (F.obj T.homology) :=
  ((T.map F).exact_iff_isZero_homology.mp h).of_iso (T.mapHomologyIso F).symm

/-- A presheaf of modules whose sections are all zero objects is a zero object. -/
theorem isZero_of_isZero_obj {M : PresheafOfModules.{z} R₀}
    (h : ∀ U : Cᵒᵖ, IsZero ((PresheafOfModules.evaluation R₀ U).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  exact PresheafOfModules.hom_ext fun U => (h U).eq_of_src _ _

/-- A short complex of presheaves of modules which is exact on sections over every object of the
site is exact. -/
theorem exact_of_exact_obj (T : ShortComplex (PresheafOfModules.{z} R₀))
    (h : ∀ U : Cᵒᵖ, (T.map (PresheafOfModules.evaluation R₀ U)).Exact) : T.Exact := by
  rw [T.exact_iff_isZero_homology]
  refine isZero_of_isZero_obj fun U => ?_
  exact isZero_obj_homology_of_exact_map _ T (h U)

end Objectwise

/-! ### Exactness of the presentation of `X[S]`

The presentation of `X[S]` in degree `n` has, over an object `U` of the site, the sections
`⨁_{s} s · X^{n - deg s}(U)`: a direct sum of pieces of `X`. Exactness in the coefficients is
therefore componentwise. -/

section Presentation

variable [HasWeakSheafify J (Type w)] (S : SheafOfGradedSets.{w} J)
  {X Y Z : ℤ → SheafOfModules.{a} R}

/-- The map of presentations induced by a morphism of the coefficients acts componentwise. -/
theorem coeffPresAddHom_apply (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) (U : Cᵒᵖ)
    (m : coeffSections S X n U) (q : S.Index U) :
    coeffPresAddHom S g n U m q = homSections (g (n - q.1)) U (m q) := by
  induction m using _root_.DirectSum.induction_on with
  | zero => rw [map_zero]; exact (map_zero (homSections (g (n - q.1)) U)).symm
  | of p x =>
    rw [show _root_.DirectSum.of _ p x = coeffOf S X n U p.1 p.2.1 p.2.2 x from rfl,
      coeffPresAddHom_coeffOf]
    by_cases hpq : q = p
    · subst hpq
      rw [show coeffOf S Y n U q.1 q.2.1 q.2.2 (homSections (g (n - q.1)) U x) =
          _root_.DirectSum.of _ q (homSections (g (n - q.1)) U x) from rfl,
        _root_.DirectSum.of_eq_same,
        show coeffOf S X n U q.1 q.2.1 q.2.2 x = _root_.DirectSum.of _ q x from rfl,
        _root_.DirectSum.of_eq_same]
    · rw [show coeffOf S Y n U p.1 p.2.1 p.2.2 (homSections (g (n - p.1)) U x) =
          _root_.DirectSum.of _ p (homSections (g (n - p.1)) U x) from rfl,
        _root_.DirectSum.of_eq_of_ne _ _ _ hpq,
        show coeffOf S X n U p.1 p.2.1 p.2.2 x = _root_.DirectSum.of _ p x from rfl,
        _root_.DirectSum.of_eq_of_ne _ _ _ hpq,
        map_zero (homSections (g (n - q.1)) U)]
  | add m m' hm hm' =>
    rw [map_add, show (coeffPresAddHom S g n U m + coeffPresAddHom S g n U m') q =
        coeffPresAddHom S g n U m q + coeffPresAddHom S g n U m' q from rfl, hm, hm',
      show (m + m') q = m q + m' q from rfl, map_add]

/-- The map of presentations induced by an objectwise injective morphism of the coefficients is
objectwise injective: a direct sum of injective maps is injective. -/
theorem coeffPresAddHom_injective (g : ∀ k : ℤ, X k ⟶ Y k)
    (hg : ∀ (k : ℤ) (U : Cᵒᵖ), Function.Injective (homSections (g k) U)) (n : ℤ) (U : Cᵒᵖ) :
    Function.Injective (coeffPresAddHom S g n U) := by
  intro m m' hmm
  refine _root_.DirectSum.ext fun q => hg (n - q.1) U ?_
  rw [← coeffPresAddHom_apply S g n U m q, ← coeffPresAddHom_apply S g n U m' q, hmm]

/-- The presentation of `X[S]` is exact in the middle: a section of the presentation of `Y[S]`
killed by the second map comes from the presentation of `X[S]`. This is the exactness of a direct
sum of sequences of modules, assembled from the finitely many nonzero components. -/
theorem coeffPresAddHom_exists (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hex : ∀ (k : ℤ) (U : Cᵒᵖ) (y : (Y k).val.obj U), homSections (h k) U y = 0 →
      ∃ x : (X k).val.obj U, homSections (g k) U x = y)
    (n : ℤ) (U : Cᵒᵖ) (m : coeffSections S Y n U) (hm : coeffPresAddHom S h n U m = 0) :
    ∃ m' : coeffSections S X n U, coeffPresAddHom S g n U m' = m := by
  classical
  have hcomp : ∀ q : S.Index U, homSections (h (n - q.1)) U (m q) = 0 := fun q => by
    rw [← coeffPresAddHom_apply S h n U m q, hm]; rfl
  choose lift hlift using fun q : S.Index U => hex (n - q.1) U (m q) (hcomp q)
  refine ⟨∑ q ∈ DFinsupp.support m, coeffOf S X n U q.1 q.2.1 q.2.2 (lift q), ?_⟩
  rw [map_sum]
  refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) (_root_.DirectSum.sum_support_of m)
  rw [coeffPresAddHom_coeffOf, hlift q]

/-- The construction `X ↦ X[S]` sends a degreewise zero morphism of coefficients to zero. -/
theorem coeffPresMap_eq_zero (g : ∀ k : ℤ, X k ⟶ Y k) (hg : ∀ k : ℤ, g k = 0) (n : ℤ) :
    coeffPresMap S g n = 0 := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show coeffPresAddHom S g n U m = 0
  induction m using _root_.DirectSum.induction_on with
  | zero => exact map_zero _
  | of p x =>
    rw [show _root_.DirectSum.of _ p x = coeffOf S X n U p.1 p.2.1 p.2.2 x from rfl,
      coeffPresAddHom_coeffOf, show homSections (g (n - p.1)) U x = 0 from by
        rw [hg (n - p.1)]; rfl, coeffOf_zero]
  | add m m' hm hm' => rw [map_add, hm, hm', add_zero]

/-- The presentation of `X[S]` is additive in the morphism of coefficients. -/
theorem coeffPresMap_add {X Y : ℤ → SheafOfModules.{a} R} (g h : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) :
    coeffPresMap S (fun k => g k + h k) n = coeffPresMap S g n + coeffPresMap S h n := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  show coeffPresAddHom S (fun k => g k + h k) n U m =
    coeffPresAddHom S g n U m + coeffPresAddHom S h n U m
  induction m using _root_.DirectSum.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, add_zero]
  | of p x =>
    rw [show _root_.DirectSum.of _ p x = coeffOf S X n U p.1 p.2.1 p.2.2 x from rfl,
      coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf, coeffPresAddHom_coeffOf,
      show homSections (g (n - p.1) + h (n - p.1)) U x =
        homSections (g (n - p.1)) U x + homSections (h (n - p.1)) U x from rfl, coeffOf_add]
  | add m m' hm hm' =>
    rw [map_add, map_add, map_add, hm, hm']
    abel

/-- The two maps of presentations induced by a degreewise zero composite compose to zero. -/
theorem coeffPresMap_comp_eq_zero (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hgh : ∀ k : ℤ, g k ≫ h k = 0) (n : ℤ) :
    coeffPresMap S g n ≫ coeffPresMap S h n = 0 :=
  (coeffPresMap_comp S g h n).symm.trans (coeffPresMap_eq_zero S _ hgh n)

end Presentation

section PresentationExact

variable [HasWeakSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] (S : SheafOfGradedSets.{w} J)
  {X Y Z : ℤ → SheafOfModules.{a} R}

omit [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] in
/-- The presentation of `X[S]` turns a degreewise monomorphism of coefficients into a
monomorphism. -/
theorem coeffPresMap_mono (g : ∀ k : ℤ, X k ⟶ Y k) (hg : ∀ k : ℤ, Mono (g k)) (n : ℤ) :
    Mono (coeffPresMap S g n) :=
  PresheafOfModules.mono_of_injective (f := coeffPresMap S g n) fun U =>
    coeffPresAddHom_injective S g
      (fun k V => injective_of_mono_sections (g k) (hg k) V) n U

/-- The presentation of `X[S]` turns a degreewise short exact sequence of coefficients into an
exact short complex. -/
theorem coeffPresMap_exact (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hgh : ∀ k : ℤ, g k ≫ h k = 0)
    (hSE : ∀ k : ℤ, (ShortComplex.mk (g k) (h k) (hgh k)).ShortExact) (n : ℤ) :
    (ShortComplex.mk (coeffPresMap S g n) (coeffPresMap S h n)
      (coeffPresMap_comp_eq_zero S g h hgh n)).Exact := by
  refine exact_of_exact_obj _ fun U => ?_
  rw [ShortComplex.moduleCat_exact_iff]
  intro m hm
  exact coeffPresAddHom_exists S g h
    (fun k V y hy => exists_of_shortExact_sections (hSE k) V y hy) n U m hm

end PresentationExact

/-! ### Exactness of `X[S]`

Sheafification of presheaves of modules is exact, so it carries the monomorphism and the
exactness of the presentation over; the epimorphism is separate, an epimorphism of sheaves of
modules being only locally surjective on sections. -/

section Pieces

variable [HasWeakSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (S : SheafOfGradedSets.{w} J) {X Y Z : ℤ → SheafOfModules.{a} R}

omit [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] in
/-- Sheafification is compatible with the maps of presentations: the morphism of pieces induced
by a morphism of the coefficients restricts to the morphism of presentations. -/
theorem coeffPieceMap_app_coeffUnit (g : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) (U : Cᵒᵖ)
    (ζ : (coeffPres S X n).obj U) :
    (coeffPieceMap S g n).val.app U ((coeffUnit S X n).app U ζ) =
      (coeffUnit S Y n).app U ((coeffPresMap S g n).app U ζ) :=
  PresheafOfModules.unit_naturality_apply (α := 𝟙 R.obj) (φ := coeffPresMap S g n) U ζ

omit [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] in
/-- The two maps of pieces of `X[S]` induced by a degreewise zero composite compose to zero. -/
theorem coeffPieceMap_comp_eq_zero (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hgh : ∀ k : ℤ, g k ≫ h k = 0) (n : ℤ) :
    coeffPieceMap S g n ≫ coeffPieceMap S h n = 0 := by
  refine coeffPiece_hom_ext S fun U ζ => ?_
  calc (coeffPieceMap S g n ≫ coeffPieceMap S h n).val.app U ((coeffUnit S X n).app U ζ)
      = (coeffUnit S Z n).app U ((coeffPresMap S h n).app U ((coeffPresMap S g n).app U ζ)) :=
        ((congrArg (fun z => (coeffPieceMap S h n).val.app U z)
          (coeffPieceMap_app_coeffUnit S g n U ζ)).trans
            (coeffPieceMap_app_coeffUnit S h n U ((coeffPresMap S g n).app U ζ)))
    _ = 0 := (congrArg (fun z => (coeffUnit S Z n).app U z)
          (congrArg (fun φ : coeffPres S X n ⟶ coeffPres S Z n => φ.app U ζ)
            (coeffPresMap_comp_eq_zero S g h hgh n))).trans
        (map_zero ((coeffUnit S Z n).app U).hom)
    _ = (0 : coeffPiece S X n ⟶ coeffPiece S Z n).val.app U ((coeffUnit S X n).app U ζ) := rfl

omit [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] in
/-- `X[S]` turns a degreewise monomorphism of coefficients into a monomorphism. -/
theorem coeffPieceMap_mono (g : ∀ k : ℤ, X k ⟶ Y k) (hg : ∀ k : ℤ, Mono (g k)) (n : ℤ) :
    Mono (coeffPieceMap S g n) := by
  have := coeffPresMap_mono S g hg n
  show Mono ((PresheafOfModules.sheafification (𝟙 R.obj)).map (coeffPresMap S g n))
  infer_instance

/-- `X[S]` turns a degreewise short exact sequence of coefficients into an exact short
complex. -/
theorem coeffPieceMap_exact (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hgh : ∀ k : ℤ, g k ≫ h k = 0)
    (hSE : ∀ k : ℤ, (ShortComplex.mk (g k) (h k) (hgh k)).ShortExact) (n : ℤ) :
    (ShortComplex.mk (coeffPieceMap S g n) (coeffPieceMap S h n)
      (coeffPieceMap_comp_eq_zero S g h hgh n)).Exact := by
  exact (coeffPresMap_exact S g h hgh hSE n).map
    (PresheafOfModules.sheafification (𝟙 R.obj) :
      PresheafOfModules.{max w a} R.obj ⥤ SheafOfModules.{max w a} R)

/-- `X[S]` turns a degreewise epimorphism of coefficients into an epimorphism. A section of the
presentation of `Z[S]` is a finite sum of summands `s · z`, and each `z` is locally in the image
of the corresponding coefficient map; since a morphism out of `X[S]` lands in a sheaf, that is
enough to pin it down. -/
theorem coeffPieceMap_epi (h : ∀ k : ℤ, Y k ⟶ Z k) (hh : ∀ k : ℤ, Epi (h k)) (n : ℤ) :
    Epi (coeffPieceMap S h n) := by
  refine ⟨fun {W} φ ψ hφψ => ?_⟩
  refine coeffPiece_hom_ext S fun U ζ => ?_
  have key : ∀ (i : ℤ) (s : S.sheaf.obj.obj U) (hs : S.HasDegree U s i)
      (zz : (Z (n - i)).val.obj U),
      φ.val.app U ((coeffUnit S Z n).app U (coeffOf S Z n U i s hs zz)) =
        ψ.val.app U ((coeffUnit S Z n).app U (coeffOf S Z n U i s hs zz)) := by
    intro i s hs zz
    have := hh (n - i)
    have : PresheafOfModules.IsLocallySurjective J (h (n - i)).val :=
      Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi (h (n - i))
    refine Stacks.eq_of_forall_lift W.isSheaf.isSeparated (h (n - i)).val zz _ _ ?_
    intro V f m hm
    have step : ∀ χ : coeffPiece S Z n ⟶ W,
        sectionRestrict W.val f
            (χ.val.app U ((coeffUnit S Z n).app U (coeffOf S Z n U i s hs zz))) =
          χ.val.app V ((coeffPieceMap S h n).val.app V ((coeffUnit S Y n).app V
            (coeffOf S Y n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs) m))) := by
      intro χ
      calc sectionRestrict W.val f
            (χ.val.app U ((coeffUnit S Z n).app U (coeffOf S Z n U i s hs zz)))
          = χ.val.app V (sectionRestrict (coeffPiece S Z n).val f
              ((coeffUnit S Z n).app U (coeffOf S Z n U i s hs zz))) :=
            (PresheafOfModules.naturality_apply χ.val f _).symm
        _ = χ.val.app V ((coeffUnit S Z n).app V
              (coeffOf S Z n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs)
                (sectionRestrict (Z (n - i)).val f zz))) :=
            congrArg (fun y => χ.val.app V y)
              ((PresheafOfModules.naturality_apply (coeffUnit S Z n) f _).symm.trans
                (congrArg (fun y => (coeffUnit S Z n).app V y)
                  (coeffPres_sectionRestrict_coeffOf S Z n f i s hs zz)))
        _ = χ.val.app V ((coeffUnit S Z n).app V ((coeffPresMap S h n).app V
              (coeffOf S Y n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs) m))) :=
            congrArg (fun y => χ.val.app V ((coeffUnit S Z n).app V y))
              (((coeffOf_congr S Z n V i (S.hasDegree_map f hs) (S.hasDegree_map f hs) rfl
                hm.symm).trans
                (coeffPresAddHom_coeffOf S h n V i (S.sheaf.obj.map f s)
                  (S.hasDegree_map f hs) m).symm).trans
                (coeffPresMap_app S h n V
                  (coeffOf S Y n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs) m)).symm)
        _ = χ.val.app V ((coeffPieceMap S h n).val.app V ((coeffUnit S Y n).app V
              (coeffOf S Y n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs) m))) :=
            congrArg (fun y => χ.val.app V y)
              (coeffPieceMap_app_coeffUnit S h n V _).symm
    refine (step φ).trans (((step ψ).trans ?_).symm)
    exact congrArg
      (fun θ : coeffPiece S Y n ⟶ W => θ.val.app V ((coeffUnit S Y n).app V
        (coeffOf S Y n V i (S.sheaf.obj.map f s) (S.hasDegree_map f hs) m))) hφψ.symm
  have hmaps : ((φ.val.app U).hom.toAddMonoidHom.comp
        ((coeffUnit S Z n).app U).hom.toAddMonoidHom) =
      ((ψ.val.app U).hom.toAddMonoidHom.comp ((coeffUnit S Z n).app U).hom.toAddMonoidHom) :=
    coeffSections_addHom_ext S Z fun i s hs zz => key i s hs zz
  exact DFunLike.congr_fun hmaps ζ

/-- **The construction `X ↦ X[S]` is exact.** A degreewise short exact sequence of graded sheaves
of modules gives a short exact sequence of the degree-`n` pieces of the free graded modules on
`S` with those coefficients. -/
theorem coeffPiece_shortExact (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k)
    (hgh : ∀ k : ℤ, g k ≫ h k = 0)
    (hSE : ∀ k : ℤ, (ShortComplex.mk (g k) (h k) (hgh k)).ShortExact) (n : ℤ) :
    (ShortComplex.mk (coeffPieceMap S g n) (coeffPieceMap S h n)
      (coeffPieceMap_comp_eq_zero S g h hgh n)).ShortExact where
  exact := coeffPieceMap_exact S g h hgh hSE n
  mono_f := coeffPieceMap_mono S g (fun k => (hSE k).mono_f) n
  epi_g := coeffPieceMap_epi S h (fun k => (hSE k).epi_g) n

end Pieces

/-! ### `X[S]` preserves exactness

Acyclicity is exactness of short complexes which are not short exact, so `coeffPiece_shortExact`
is not by itself enough for it: that has to be upgraded to preservation of exactness, which for an
additive functor between abelian categories is `CategoryTheory.Functor.exact_tfae`. This needs
`X ↦ X[S]` as a functor on an abelian category of graded sheaves of modules, and the abelian
category used is the functor category `Discrete ℤ ⥤ SheafOfModules R` rather than the product
`ℤ → SheafOfModules R`, which Mathlib does not know to be abelian. -/

section FunctorForm

variable [HasWeakSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}]
  (S : SheafOfGradedSets.{w} J)

omit [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] in
/-- `X[S]` is additive in the morphism of coefficients. -/
theorem coeffPieceMap_add {X Y : ℤ → SheafOfModules.{a} R} (g h : ∀ k : ℤ, X k ⟶ Y k) (n : ℤ) :
    coeffPieceMap S (fun k => g k + h k) n = coeffPieceMap S g n + coeffPieceMap S h n := by
  rw [coeffPieceMap, coeffPresMap_add]
  exact (PresheafOfModules.sheafification (𝟙 R.obj)).map_add

/-- **`X ↦ X[S]` in degree `n`, as a functor.** The source is the functor category on the
discrete category of the integers, which is the abelian category of graded sheaves of
modules. -/
noncomputable def coeffPieceFunctor (n : ℤ) :
    (Discrete ℤ ⥤ SheafOfModules.{a} R) ⥤ SheafOfModules.{max w a} R where
  obj X := coeffPiece S (fun k => X.obj ⟨k⟩) n
  map φ := coeffPieceMap S (fun k => φ.app ⟨k⟩) n
  map_id _ := coeffPieceMap_id S n
  map_comp _ _ := coeffPieceMap_comp S _ _ n

/-- The functor `X ↦ X[S]` in degree `n` is additive. -/
instance coeffPieceFunctor_additive (n : ℤ) :
    Functor.Additive (coeffPieceFunctor S n :
      (Discrete ℤ ⥤ SheafOfModules.{a} R) ⥤ SheafOfModules.{max w a} R) where
  map_add := coeffPieceMap_add S _ _ n

/-- A degreewise short complex of graded sheaves of modules, as a short complex in the functor
category on the discrete category of the integers. -/
noncomputable def coeffDiscreteComplex {X Y Z : ℤ → SheafOfModules.{a} R}
    (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k) (hgh : ∀ k : ℤ, g k ≫ h k = 0) :
    ShortComplex (Discrete ℤ ⥤ SheafOfModules.{a} R) :=
  ShortComplex.mk
    (Discrete.natTrans (F := Discrete.functor X) (G := Discrete.functor Y) fun k => g k.as)
    (Discrete.natTrans (F := Discrete.functor Y) (G := Discrete.functor Z) fun k => h k.as)
    (NatTrans.ext (funext fun k => hgh k.as))

omit [HasSheafify J AddCommGrpCat.{a}] [J.WEqualsLocallyBijective AddCommGrpCat.{a}] in
/-- `X ↦ X[S]` applied to the short complex on the discrete category **is** the degreewise short
complex of the pieces. -/
theorem coeffDiscreteComplex_map {X Y Z : ℤ → SheafOfModules.{a} R}
    (g : ∀ k : ℤ, X k ⟶ Y k) (h : ∀ k : ℤ, Y k ⟶ Z k) (hgh : ∀ k : ℤ, g k ≫ h k = 0) (n : ℤ) :
    (coeffDiscreteComplex g h hgh).map (coeffPieceFunctor S n :
        (Discrete ℤ ⥤ SheafOfModules.{a} R) ⥤ SheafOfModules.{max w a} R) =
      ShortComplex.mk (coeffPieceMap S g n) (coeffPieceMap S h n)
        (coeffPieceMap_comp_eq_zero S g h hgh n) := rfl

/-- `X ↦ X[S]` carries a short exact sequence of graded sheaves of modules to a short exact
sequence; this is `coeffPiece_shortExact` in functor form. -/
theorem coeffPieceFunctor_shortExact (n : ℤ)
    (T : ShortComplex (Discrete ℤ ⥤ SheafOfModules.{a} R)) (hT : T.ShortExact) :
    (T.map (coeffPieceFunctor S n :
      (Discrete ℤ ⥤ SheafOfModules.{a} R) ⥤ SheafOfModules.{max w a} R)).ShortExact := by
  have hz : ∀ k : ℤ, T.f.app ⟨k⟩ ≫ T.g.app ⟨k⟩ = 0 := fun k =>
    (T.map ((CategoryTheory.evaluation (Discrete ℤ) (SheafOfModules.{a} R)).obj ⟨k⟩)).zero
  exact coeffPiece_shortExact S (fun k => T.f.app ⟨k⟩) (fun k => T.g.app ⟨k⟩) hz
    (fun k => hT.map_of_exact
      ((CategoryTheory.evaluation (Discrete ℤ) (SheafOfModules.{a} R)).obj ⟨k⟩)) n

omit [HasWeakSheafify J (Type w)] [HasSheafify J AddCommGrpCat.{max w a}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max w a}] in
/-- A short complex of graded sheaves of modules which is exact in every degree is exact. -/
theorem exact_of_exact_app (T : ShortComplex (Discrete ℤ ⥤ SheafOfModules.{a} R))
    (h : ∀ k : Discrete ℤ, (T.map
      ((CategoryTheory.evaluation (Discrete ℤ) (SheafOfModules.{a} R)).obj k)).Exact) :
    T.Exact := by
  rw [T.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  refine NatTrans.ext (funext fun k => ?_)
  exact (isZero_obj_homology_of_exact_map _ T (h k)).eq_of_src _ _

/-- **`X ↦ X[S]` preserves exactness.** A short complex of graded sheaves of modules which is
exact in every degree gives an exact short complex of the degree-`n` pieces. -/
theorem coeffPiece_exact {X Y Z : ℤ → SheafOfModules.{a} R} (g : ∀ k : ℤ, X k ⟶ Y k)
    (h : ∀ k : ℤ, Y k ⟶ Z k) (hgh : ∀ k : ℤ, g k ≫ h k = 0)
    (hex : ∀ k : ℤ, (ShortComplex.mk (g k) (h k) (hgh k)).Exact) (n : ℤ) :
    (ShortComplex.mk (coeffPieceMap S g n) (coeffPieceMap S h n)
      (coeffPieceMap_comp_eq_zero S g h hgh n)).Exact := by
  have hiff := (Functor.exact_tfae (coeffPieceFunctor S n :
    (Discrete ℤ ⥤ SheafOfModules.{a} R) ⥤ SheafOfModules.{max w a} R)).out 1 2
  have hse : ∀ T' : ShortComplex (Discrete ℤ ⥤ SheafOfModules.{a} R), T'.ShortExact →
      (T'.map (coeffPieceFunctor S n : (Discrete ℤ ⥤ SheafOfModules.{a} R) ⥤
        SheafOfModules.{max w a} R)).ShortExact :=
    fun T' hT' => coeffPieceFunctor_shortExact S n T' hT'
  have hT : (coeffDiscreteComplex g h hgh).Exact := exact_of_exact_app _ fun k => hex k.as
  have hmapped := hiff.mp hse (coeffDiscreteComplex g h hgh) hT
  exact (coeffDiscreteComplex_map S g h hgh n) ▸ hmapped

end FunctorForm

end SheafOfModules

end
