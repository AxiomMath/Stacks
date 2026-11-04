module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Shift.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfPresheavesOfModules.TermFunctorExactness
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory

/-!
# Derived Hom along a ring homomorphism (Stacks chapter Dualizing Complexes)

For a homomorphism of rings `f : A →+* B`, coextension of scalars is the functor
`Hom_A(B, -) : Mod(A) ⥤ Mod(B)`, right adjoint to restriction of scalars. Both functors are
exact, but only the derived functor of coextension is interesting: this file constructs the
total right derived functor `RHom_A(B, -) : D(A) ⥤ D(B)` and shows it is right adjoint to the
functor induced on derived categories by restriction of scalars.

The construction is a Kan extension along the localization from the homotopy category, and its
existence comes from K-injective resolutions of unbounded complexes of modules; so the
adjunction below is a statement about the canonical derived functor, not about a separately
chosen model of it. The proof exhibits, at each object, a cocone that computes the right
derived value (on a K-injective resolution, which is terminal among quasi-isomorphisms out of
the object) and a cone that computes the left derived value of the exact functor restriction
of scalars (where every quasi-isomorphism is already inverted), and then appeals to the
general comparison of derived adjoints.

Composing along `A → B → C` is compatible with the construction: both
`RHom_B(C, -) ∘ RHom_A(B, -)` and `RHom_A(C, -)` are right adjoint to the same functor, namely
the derived functor of restriction along the composite, so they are isomorphic.

## Main definitions

* `Dualizing.homotopyAdjunction` — the adjunction on homotopy categories induced degreewise by
  an additive adjunction.
* `Dualizing.derivedHom` — the derived coextension-of-scalars functor `RHom_A(B, -)`.

## Main results

* `Dualizing.coextendScalars_hasPointwiseRightDerivedFunctor` — coextension of scalars admits
  a pointwise total right derived functor.
* `Dualizing.restrictScalarsDerived_adj_derivedHom` — restriction of scalars on derived
  categories is left adjoint to derived Hom.
* `Dualizing.derivedHomCompIso` — derived Hom is compatible with composition of ring maps.

## Implementation notes

`derivedHom` is stated for arbitrary (not necessarily commutative) rings and with independent
universe parameters for the source ring, the target ring and the module size.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0C0F](https://stacks.math.columbia.edu/tag/0C0F)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe u v u' w x y z

namespace Dualizing

/-- Coextension of scalars along a ring homomorphism is an additive functor. -/
local instance {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    (ModuleCat.coextendScalars.{u, u', w} f).Additive where
  map_add := by intros; ext; rfl

/-- Restriction of scalars along a ring homomorphism preserves finite limits. -/
local instance {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{max v u u'} f) := by
  constructor
  intro J _ _
  constructor
  intro F
  infer_instance

/-- Restriction of scalars along a ring homomorphism preserves finite colimits. -/
local instance {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    Limits.PreservesFiniteColimits (ModuleCat.restrictScalars.{max v u u'} f) := by
  constructor
  intro J _ _
  constructor
  intro F
  infer_instance

/-- The adjunction on homotopy categories induced degreewise by an additive adjunction. -/
noncomputable def homotopyAdjunction
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) {ι : Type*} (c : ComplexShape ι) :
    F.mapHomotopyCategory c ⊣ G.mapHomotopyCategory c where
  unit := Quotient.natTransLift _
    (whiskerRight (adj.mapHomologicalComplex c).unit (HomotopyCategory.quotient C c))
  counit := Quotient.natTransLift _
    (whiskerRight (adj.mapHomologicalComplex c).counit (HomotopyCategory.quotient D c))
  left_triangle_components := by
    rintro ⟨X⟩
    exact ((HomotopyCategory.quotient D c).map_comp _ _).symm.trans
      ((congrArg _ ((adj.mapHomologicalComplex c).left_triangle_components X)).trans
        ((HomotopyCategory.quotient D c).map_id _))
  right_triangle_components := by
    rintro ⟨Y⟩
    exact ((HomotopyCategory.quotient C c).map_comp _ _).symm.trans
      ((congrArg _ ((adj.mapHomologicalComplex c).right_triangle_components Y)).trans
        ((HomotopyCategory.quotient C c).map_id _))

/-- For a functor `F` inverting a morphism property `W`, the cone over the category of
`W`-morphisms into `X` whose vertex is `F X` and whose projections are the inverses of the
images of those morphisms. -/
noncomputable def coneOfInvertedMorphisms
    {C : Type w} {D : Type x} [Category.{y} C] [Category.{z} D]
    (F : CategoryTheory.Functor C D)
    (W : MorphismProperty C) (hF : W.IsInvertedBy F) (X : C) :
    Limits.Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) where
  pt := F.obj X
  π :=
    { app := fun s ↦ by
        letI : IsIso (F.map s.hom) := hF s.hom s.prop
        exact (asIso (F.map s.hom)).inv
      naturality := fun s t u ↦ by
        have : IsIso (F.map s.hom) := hF s.hom s.prop
        have : IsIso (F.map t.hom) := hF t.hom t.prop
        dsimp
        apply (cancel_mono (F.map t.hom)).1
        simp only [Category.id_comp]
        rw [Category.assoc, ← F.map_comp, MorphismProperty.Over.w u,
          IsIso.inv_hom_id, IsIso.inv_hom_id] }

/-- A functor inverting `W` is its own left derived functor: the cone `coneOfInvertedMorphisms`
computes the left derived value at every object, the identity morphism providing the required
initial index. -/
lemma coneOfInvertedMorphisms_isLeftDerivedValueAt
    {C : Type w} {D : Type x} [Category.{y} C] [Category.{z} D]
    (F : CategoryTheory.Functor C D)
    (W : MorphismProperty C) [W.ContainsIdentities] (hF : W.IsInvertedBy F) (X : C) :
    F.IsLeftDerivedValueAt W X (coneOfInvertedMorphisms F W hF X) := by
  let s₀ : W.Over ⊤ X := MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)
  let v : ∀ s : W.Over ⊤ X, s ⟶ s₀ := fun s =>
    MorphismProperty.Over.homMk (A := s) (B := s₀) s.hom (by
      show s.hom ≫ 𝟙 X = s.hom
      simp)
  refine ⟨s₀, F.map s₀.hom, ?_, fun s ↦ ?_⟩
  · dsimp [coneOfInvertedMorphisms]
    have : IsIso (F.map s₀.hom) := hF s₀.hom s₀.prop
    simp
  · refine ⟨s, 𝟙 s, v s, ?_⟩
    have : IsIso (F.map s.hom) := hF s.hom s.prop
    dsimp [coneOfInvertedMorphisms]
    calc
      F.map (𝟙 s.left) = 𝟙 (F.obj s.left) := by simp
      _ =
          F.map ((v s).left ≫ s₀.hom) ≫ inv (F.map s.hom) := by
            rw [MorphismProperty.Over.w (v s)]
            simp
      _ = F.map (v s).left ≫ F.map s₀.hom ≫ inv (F.map s.hom) := by
            simp only [Functor.map_comp, Category.assoc]

/-- If the category of `W`-morphisms out of `X` has a terminal object `t₀`, then the cocone on the
diagram of `F` indexed by that category which is induced by `t₀` computes the right derived value
of `F` at `X`. -/
lemma coconeOfTerminalUnder_isRightDerivedValueAt
    {C : Type w} {D : Type x} [Category.{y} C] [Category.{z} D]
    (F : CategoryTheory.Functor C D) (W : MorphismProperty C)
    [W.ContainsIdentities] (X : C) (t₀ : W.Under ⊤ X) (ht : Limits.IsTerminal t₀) :
    F.IsRightDerivedValueAt W X
      (Limits.coconeOfDiagramTerminal ht
        (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) := by
  refine ⟨t₀, 𝟙 _, (Category.id_comp _).trans (by simp), fun s => ?_⟩
  refine ⟨t₀, ht.from s, ht.from t₀, ?_⟩
  show F.map (ht.from s).right =
    F.map (ht.from s).right ≫ 𝟙 _ ≫ F.map (ht.from t₀).right
  simp

/-- A quasi-isomorphism `q : K ⟶ I` in the homotopy category with `I` K-injective is terminal
among the quasi-isomorphisms out of `K`: by K-injectivity every other quasi-isomorphism out of
`K` admits a unique morphism to `q` over `K`. -/
noncomputable def isTerminalUnderKInjective
    {C : Type w} [Category.{y} C] [Abelian C] [HasDerivedCategory C]
    {K : HomotopyCategory C (ComplexShape.up ℤ)} (I : CochainComplex C ℤ)
    [I.IsKInjective] (q : K ⟶ (HomotopyCategory.quotient C (.up ℤ)).obj I)
    (hq : HomotopyCategory.quasiIso C (.up ℤ) q) :
    Limits.IsTerminal (MorphismProperty.Under.mk ⊤ q hq) := by
  have hI : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).isLocal
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I) :=
    ((CochainComplex.isKInjective_tfae I).out 1 2).mp (by assumption)
  exact Limits.IsTerminal.ofUniqueHom
    (fun s ↦ MorphismProperty.Under.homMk _ ((hI s.hom s.prop).2 q).choose_spec)
    (fun s a ↦ MorphismProperty.Under.Hom.ext
      ((hI s.hom s.prop).1 ((MorphismProperty.Under.w a).trans
        ((hI s.hom s.prop).2 q).choose_spec.symm)))

/-- Coextension admits a total right derived functor, computed on K-injective resolutions. -/
theorem coextendScalars_hasPointwiseRightDerivedFunctor
    {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh).HasPointwiseRightDerivedFunctor
        (HomotopyCategory.quasiIso (ModuleCat.{max v u u'} A) (.up ℤ)) := by
  have : EnoughInjectives (ModuleCat.{max v u u'} A) := ModuleCat.enoughInjectives.{max v u', u} A
  exact (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max v u u', max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1),
        max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1),
        max (u + 1) (v + 1) (u' + 1)}
      ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ by
        obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
        exact ⟨I, q, hI, hq⟩)).1

/-- The derived coextension-of-scalars functor
`RHom_A(B, -) : D(A) ⥤ D(B)` associated to a ring homomorphism `f : A →+* B`. -/
noncomputable def derivedHom {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    DerivedCategory (ModuleCat.{max v u u'} A) ⥤
      DerivedCategory (ModuleCat.{max v u u'} B) := by
  have := coextendScalars_hasPointwiseRightDerivedFunctor.{u, v, u'} f
  exact ((ModuleCat.coextendScalars.{u, u', max v u u'} f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max v u u'} A) (ComplexShape.up ℤ))


/-- Derived coextension of scalars `RHom_A(B, -)` is right adjoint to restriction of scalars from
`D(B)` to `D(A)`, at the standard model of the derived category. -/
theorem restrictScalarsDerived_adj_derivedHom
    {A : Type u} {B : Type u'} [Ring A] [Ring B] (f : A →+* B) :
    Nonempty ((ModuleCat.restrictScalars.{max v u u'} f).mapDerivedCategory ⊣
      derivedHom.{u, v, u'} f) := by
  let AMod := ModuleCat.{max v u u'} A
  let BMod := ModuleCat.{max v u u'} B
  let F₀ := ModuleCat.coextendScalars.{u, u', max v u u'} f
  let G₀ := ModuleCat.restrictScalars.{max v u u'} f
  let W := HomotopyCategory.quasiIso AMod (ComplexShape.up ℤ)
  let W' := HomotopyCategory.quasiIso BMod (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := AMod)
  let Q' := DerivedCategory.Qh (C := BMod)
  let F := F₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let G := G₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let LG := G₀.mapDerivedCategory
  let α := G₀.mapDerivedCategoryFactorsh.hom
  have : EnoughInjectives AMod := ModuleCat.enoughInjectives.{max v u', u} A
  let hPoint := hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      max v u u', max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1),
      max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1), max (u + 1) (v + 1) (u' + 1)}
    (F ⋙ Q') (fun K ↦ by
      obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨I, q, hI, hq⟩)
  have : (F ⋙ Q').HasPointwiseRightDerivedFunctor W := hPoint.1
  let RF := (F ⋙ Q').totalRightDerived Q W
  let β := (F ⋙ Q').totalRightDerivedUnit Q W
  have : RF.IsRightDerivedFunctor β W := by
    dsimp [RF, β, F, Q', Q, W]
    infer_instance
  let adj := homotopyAdjunction
    (ModuleCat.restrictCoextendScalarsAdj.{max v u u'} f) (ComplexShape.up ℤ)
  have hInv : W'.IsInvertedBy (G ⋙ Q) := by
    dsimp [G, Q, W']
    exact Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso G₀
  have hRF : ∀ K : HomotopyCategory AMod (ComplexShape.up ℤ),
      ∃ (c : Limits.Cocone (MorphismProperty.Under.forget W ⊤ K ⋙
        Under.forget K ⋙ F ⋙ Q')),
        ∃ (_ : (F ⋙ Q').IsRightDerivedValueAt W K c),
          ∃ (e : c.pt ≅ RF.obj (Q.obj K)),
            ∀ s : W.Under ⊤ K,
              c.ι.app s ≫ e.hom ≫ RF.map (Q.map s.hom) = β.app s.right := by
    intro K
    obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective Kc
    let qh := (HomotopyCategory.quotient AMod (ComplexShape.up ℤ)).map q
    have hqh : W qh := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
    let t₀ : W.Under ⊤ _ := MorphismProperty.Under.mk ⊤ qh hqh
    let ht := isTerminalUnderKInjective I qh hqh
    let c := Limits.coconeOfDiagramTerminal ht
      (MorphismProperty.Under.forget W ⊤ _ ⋙ Under.forget _ ⋙ F ⋙ Q')
    have hc := coconeOfTerminalUnder_isRightDerivedValueAt (F ⋙ Q') W _ t₀ ht
    have : IsIso (β.app t₀.right) := hPoint.2 Q RF β I hI
    have : IsIso (Q.map t₀.hom) := Localization.inverts Q W t₀.hom t₀.prop
    let eRF : _ ≅ _ := asIso (RF.map (Q.map t₀.hom))
    let eβ : _ ≅ _ := asIso (β.app t₀.right)
    refine ⟨c, hc, eβ ≪≫ eRF.symm, fun s ↦ ?_⟩
    have hcomp : s.hom ≫ (ht.from s).right = t₀.hom := MorphismProperty.Under.w (ht.from s)
    have hnat : (F ⋙ Q').map ((ht.from s).right) ≫ β.app t₀.right =
        β.app s.right ≫ RF.map (Q.map ((ht.from s).right)) := β.naturality ((ht.from s).right)
    have : IsIso (Q.map s.hom) := Localization.inverts Q W s.hom s.prop
    have hComp : RF.map (Q.map s.hom) ≫ RF.map (Q.map ((ht.from s).right)) = eRF.hom := by
      simp only [eRF, asIso_hom, ← Functor.map_comp, hcomp]
    have hcancel :
        RF.map (Q.map ((ht.from s).right)) ≫ eRF.inv ≫ RF.map (Q.map s.hom) = 𝟙 _ := by
      rw [← cancel_epi (RF.map (Q.map s.hom)), reassoc_of% hComp, Iso.hom_inv_id_assoc]
      exact (Category.comp_id _).symm
    show Q'.map (F.map (ht.from s).right) ≫ (β.app t₀.right ≫ eRF.inv) ≫
      RF.map (Q.map s.hom) = _
    rw [Category.assoc, reassoc_of% hnat, hcancel, Category.comp_id]
  have hLG : ∀ M : HomotopyCategory BMod (ComplexShape.up ℤ),
      ∃ (d : Limits.Cone (MorphismProperty.Over.forget W' ⊤ M ⋙
        Over.forget M ⋙ G ⋙ Q)),
        ∃ (_ : (G ⋙ Q).IsLeftDerivedValueAt W' M d),
          ∃ (e : LG.obj (Q'.obj M) ≅ d.pt),
            ∀ t : W'.Over ⊤ M,
              LG.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left := by
    intro M
    refine ⟨coneOfInvertedMorphisms (G ⋙ Q) W' hInv M,
      coneOfInvertedMorphisms_isLeftDerivedValueAt (G ⋙ Q) W' hInv M,
      G₀.mapDerivedCategoryFactorsh.app M, fun t ↦ ?_⟩
    have : IsIso ((G ⋙ Q).map t.hom) := hInv t.hom t.prop
    have hn : LG.map (Q'.map t.hom) ≫ α.app M = α.app t.left ≫ (G ⋙ Q).map t.hom :=
      α.naturality t.hom
    show LG.map (Q'.map t.hom) ≫ α.app M ≫ inv ((G ⋙ Q).map t.hom) = _
    rw [reassoc_of% hn, ← Functor.comp_map, IsIso.hom_inv_id, Category.comp_id]
  show Nonempty (LG ⊣ RF)
  obtain ⟨adjDerived, _, _⟩ :=
    CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      adj W W' Q Q' RF β LG α hRF hLG
  exact ⟨adjDerived⟩

/-- The commutation of derived coextension of scalars with the shift, obtained as the right
adjoint of the functor induced on derived categories by restriction of scalars.

Marked `@[instance_reducible]` so that a `let` of it is seen through when the shift of a derived
Hom has to be matched with the derived Hom of a shift. -/
@[instance_reducible]
public noncomputable def derivedHomCommShift
    {A : Type u} {B : Type u'} [CommRing A] [CommRing B] (f : A →+* B) :
    (derivedHom.{u, v, u'} f).CommShift ℤ :=
  (Classical.choice (restrictScalarsDerived_adj_derivedHom.{u, v, u'} f)).rightAdjointCommShift ℤ


/-- A `B`-module which becomes finite after restriction of scalars along a ring homomorphism
`f : A →+* B` is already finite over `B`: a finite `A`-generating set generates it over the
larger ring. -/
theorem finite_of_restrictScalars_finite {A : Type u} {B : Type u'} [Ring A] [Ring B]
    (f : A →+* B) (M : ModuleCat.{w} B)
    [Module.Finite A ((ModuleCat.restrictScalars f).obj M)] : Module.Finite B M := by
  let : SMul A B := ⟨fun a b ↦ f a * b⟩
  have : IsScalarTower A B ((ModuleCat.restrictScalars f).obj M) :=
    ⟨fun a b x ↦ show (f a * b) • (x : M) = f a • b • (x : M) from mul_smul _ _ _⟩
  exact Module.Finite.of_restrictScalars_finite A B ((ModuleCat.restrictScalars f).obj M)

section Composition

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- For ring maps `A → B → C`, the composite `RHom_B(C, -) ∘ RHom_A(B, -)` is naturally
isomorphic to `RHom_A(C, -)`. -/
@[stacks 0C0F]
theorem derivedHomCompIso (f : A →+* B) (g : B →+* C) :
    Nonempty
      (derivedHom.{u, v} f ⋙ derivedHom.{u, v} g ≅
        derivedHom.{u, v} (g.comp f)) := by
  let e := mapDerivedCategoryCompNatIso
    (ModuleCat.restrictScalars.{max v u} g)
    (ModuleCat.restrictScalars.{max v u} f)
    (ModuleCat.restrictScalars.{max v u} (g.comp f))
    (ModuleCat.restrictScalarsComp.{max v u} f g).symm
  obtain ⟨adjF⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} f
  obtain ⟨adjG⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} g
  obtain ⟨adjH⟩ := restrictScalarsDerived_adj_derivedHom.{u, v} (g.comp f)
  exact ⟨((adjG.comp adjF).ofNatIsoLeft e).rightAdjointUniq adjH⟩

end Composition

end Dualizing
