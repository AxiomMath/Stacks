module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The Gabriel--Popescu embedding on unbounded derived categories

Let `C` be a Grothendieck abelian category and `G` a separator of `C`. The Gabriel--Popescu
theorem presents `C` as a localization of the category of right modules over `End G`: the
functor `Hom(G, -) : C ⥤ Mod (End G)ᵐᵖ` is fully faithful and has an exact left adjoint
`- ⊗ G`. This file upgrades that presentation to the unbounded derived categories.

The embedding `Hom(G, -)`, viewed as a functor from the homotopy category of cochain
complexes to `D(Mod (End G)ᵐᵖ)`, has a *pointwise* right derived functor
`R : D(C) ⥤ D(Mod (End G)ᵐᵖ)`: every complex in `C` admits a quasi-isomorphism into a
K-injective complex, and such a complex computes the derived functor. The left adjoint is
exact, so it induces a functor `D(Mod (End G)ᵐᵖ) ⥤ D(C)` with no derivation needed, and this
induced functor is automatically a left derived functor: its value at a complex is computed by
the constant pro-object, because the functor already inverts quasi-isomorphisms. Feeding these
two pointwise computations into the derived-adjunction criterion produces an adjunction
`derivedTensorObj G hG ⊣ R` on derived categories.

Finally the counit of that adjunction is an isomorphism. It is an isomorphism at a K-injective
complex `I`, because there the derived unit `β.app I` is invertible and the counit of the
underlying adjunction of complexes is invertible degreewise; and every object of `D(C)` is
isomorphic to one of that form, since a complex is quasi-isomorphic to its K-injective
resolution. An adjunction with invertible counit has fully faithful right adjoint, so `R` is a
fully faithful embedding of `D(C)` into `D(Mod (End G)ᵐᵖ)`, which is the derived form of
Gabriel--Popescu.

## Main definitions

* `Stacks.Injectives.derivedTensorObj`: the functor on derived categories induced by the exact
  Gabriel--Popescu left adjoint `- ⊗ G`.
* `Stacks.Injectives.DerivedGabrielPopescuData`: the derived Gabriel--Popescu situation, namely
  a right derived functor of `Hom(G, -)` together with its comparison map, the adjunction
  against `derivedTensorObj G hG`, full faithfulness, and invertibility of the counit.

## Main results

* `Stacks.Injectives.exists_derivedGabrielPopescuData`: such a situation exists for every
  separator of a Grothendieck abelian category.

## Implementation notes

The left-hand functor is pinned to the one induced by `- ⊗ G` rather than left over as an
arbitrary left derived functor, so that the identification of `(- ⊗ G) ∘ R` with the identity
can be recorded as invertibility of the counit of a *named* adjunction; this keeps both the
naturality of that identification and its compatibility with the adjunction, which an equality
of functors would lose.

## References

* [Stacks Project, Tag 0F5V](https://stacks.math.columbia.edu/tag/0F5V)
* Serpé, *Resolution of unbounded complexes in Grothendieck categories*, Corollary 4.1
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.Injectives

variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C]

/-- An adjunction between additive functors of abelian categories descends to the homotopy
categories of cochain complexes: both functors are the ones induced degreewise, and the unit
and counit are the homotopy classes of the unit and counit of the degreewise adjunction. -/
private noncomputable def homotopyAdjunction
    {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive]
    (adj : L ⊣ R) :
    L.mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      R.mapHomotopyCategory (ComplexShape.up ℤ) where
  unit := Quotient.natTransLift _
    (Functor.whiskerRight (adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit
      (HomotopyCategory.quotient A (ComplexShape.up ℤ)))
  counit := Quotient.natTransLift _
    (Functor.whiskerRight (adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit
      (HomotopyCategory.quotient B (ComplexShape.up ℤ)))
  left_triangle_components := by
    rintro ⟨X⟩
    exact ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      ((congrArg _ ((adj.mapHomologicalComplex
        (ComplexShape.up ℤ)).left_triangle_components X)).trans
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map_id _))
  right_triangle_components := by
    rintro ⟨Y⟩
    exact ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_comp _ _).symm.trans
      ((congrArg _ ((adj.mapHomologicalComplex
        (ComplexShape.up ℤ)).right_triangle_components Y)).trans
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_id _))

/-- The counit of the descended adjunction is, at the homotopy class of a complex, the homotopy
class of the counit of the degreewise adjunction of complexes. -/
private lemma homotopyAdjunction_counit_app
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] (adj : L ⊣ R)
    (I : CochainComplex B ℤ) :
  (homotopyAdjunction adj).counit.app
        ((HomotopyCategory.quotient B _).obj I) =
      (HomotopyCategory.quotient B _).map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) := rfl

/-- A quasi-isomorphism into a K-injective complex is a terminal object of the category of
quasi-isomorphisms out of its source: any other quasi-isomorphism out of that source maps to
it, uniquely up to the relation used in the localization. -/
noncomputable def isTerminalUnderKInjective
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    {K : HomotopyCategory A (ComplexShape.up ℤ)} (I : CochainComplex A ℤ)
    [I.IsKInjective] (q : K ⟶ (HomotopyCategory.quotient A (.up ℤ)).obj I)
    (hq : HomotopyCategory.quasiIso A (.up ℤ) q) :
    Limits.IsTerminal (MorphismProperty.Under.mk ⊤ q hq) := by
  have hI : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).isLocal
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) :=
    ((CochainComplex.isKInjective_tfae I).out 1 2).mp (by assumption)
  exact Limits.IsTerminal.ofUniqueHom
    (fun s ↦ MorphismProperty.Under.homMk _ ((hI s.hom s.prop).2 q).choose_spec)
    (fun s a ↦ MorphismProperty.Under.Hom.ext
      ((hI s.hom s.prop).1 ((MorphismProperty.Under.w a).trans
        ((hI s.hom s.prop).2 q).choose_spec.symm)))

/-- For a functor inverting a morphism property `W`, the cone over the category of
`W`-morphisms into `X` whose vertex is `F X` and whose projections are the inverses of the
images of those morphisms. -/
noncomputable def coneOfInvertedMorphisms
    {A : Type*} {B : Type*} [Category A] [Category B]
    (F : CategoryTheory.Functor A B) (W : MorphismProperty A)
    (hF : W.IsInvertedBy F) (X : A) :
    Limits.Cone (MorphismProperty.Over.forget W ⊤ X ⋙ Over.forget X ⋙ F) where
  pt := F.obj X
  π :=
    { app := fun s ↦ by
        letI : IsIso (F.map s.hom) := hF s.hom s.prop
        exact (asIso (F.map s.hom)).inv
      naturality := fun s t u ↦ by
        let : IsIso (F.map s.hom) := hF s.hom s.prop
        let : IsIso (F.map t.hom) := hF t.hom t.prop
        dsimp
        apply (cancel_mono (F.map t.hom)).1
        simp only [Category.id_comp]
        rw [Category.assoc, ← F.map_comp, MorphismProperty.Over.w u,
          IsIso.inv_hom_id, IsIso.inv_hom_id] }

/-- A functor inverting `W` is its own left derived functor: the cone of
`coneOfInvertedMorphisms` computes the left derived value at every object, the identity
morphism providing the required initial index. -/
lemma coneOfInvertedMorphisms_isLeftDerivedValueAt
    {A : Type*} {B : Type*} [Category A] [Category B]
    (F : CategoryTheory.Functor A B) (W : MorphismProperty A)
    [W.ContainsIdentities] (hF : W.IsInvertedBy F) (X : A) :
    F.IsLeftDerivedValueAt W X (coneOfInvertedMorphisms F W hF X) := by
  let s₀ : W.Over ⊤ X := MorphismProperty.Over.mk ⊤ (𝟙 X) (MorphismProperty.id_mem W X)
  let v : ∀ s : W.Over ⊤ X, s ⟶ s₀ := fun s =>
    MorphismProperty.Over.homMk (A := s) (B := s₀) s.hom (by
      show s.hom ≫ 𝟙 X = s.hom
      simp)
  refine ⟨s₀, F.map s₀.hom, ?_, fun s ↦ ?_⟩
  · dsimp [coneOfInvertedMorphisms]
    let : IsIso (F.map s₀.hom) := hF s₀.hom s₀.prop
    simp
  · refine ⟨s, 𝟙 s, v s, ?_⟩
    let : IsIso (F.map s.hom) := hF s.hom s.prop
    dsimp [coneOfInvertedMorphisms]
    calc
      F.map (𝟙 s.left) = 𝟙 (F.obj s.left) := by simp
      _ = F.map ((v s).left ≫ s₀.hom) ≫ inv (F.map s.hom) := by
        rw [MorphismProperty.Over.w (v s)]
        simp
      _ = F.map (v s).left ≫ F.map s₀.hom ≫ inv (F.map s.hom) := by
        simp only [Functor.map_comp, Category.assoc]

/-- If the category of `W`-morphisms out of `X` has a terminal object, then the cocone it
determines computes the right derived value of any functor at `X`. -/
lemma coconeOfTerminalUnder_isRightDerivedValueAt
    {A : Type*} {B : Type*} [Category A] [Category B]
    (F : CategoryTheory.Functor A B) (W : MorphismProperty A)
    [W.ContainsIdentities] (X : A) (t₀ : W.Under ⊤ X)
    (ht : Limits.IsTerminal t₀) :
    F.IsRightDerivedValueAt W X
      (Limits.coconeOfDiagramTerminal ht
        (MorphismProperty.Under.forget W ⊤ X ⋙ Under.forget X ⋙ F)) := by
  refine ⟨t₀, 𝟙 _, (Category.id_comp _).trans (by simp), fun s => ?_⟩
  refine ⟨t₀, ht.from s, ht.from t₀, ?_⟩
  show F.map (ht.from s).right =
    F.map (ht.from s).right ≫ 𝟙 _ ≫ F.map (ht.from t₀).right
  simp

/-- The functor on unbounded derived categories induced by the exact Gabriel--Popescu left
adjoint `- ⊗ G : Mod (End G)ᵐᵖ ⥤ C`. Since that functor is exact it inverts
quasi-isomorphisms, so no derivation is involved: it is applied degreewise to complexes. -/
noncomputable def derivedTensorObj (G : C) (hG : IsSeparator G) :
    DerivedCategory (ModuleCat.{v} (End G)ᵐᵒᵖ) ⥤ DerivedCategory C := by
  letI : PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj G) :=
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits G hG
  letI : PreservesBinaryBiproducts (IsGrothendieckAbelian.tensorObj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  letI : (IsGrothendieckAbelian.tensorObj G).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  exact (IsGrothendieckAbelian.tensorObj G).mapDerivedCategory

/-- The functor induced by the Gabriel--Popescu left adjoint commutes with the shift. -/
noncomputable instance derivedTensorObj_commShift (G : C) (hG : IsSeparator G) :
    (derivedTensorObj G hG).CommShift ℤ :=
  letI : PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj G) :=
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits G hG
  letI : PreservesBinaryBiproducts (IsGrothendieckAbelian.tensorObj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  letI : (IsGrothendieckAbelian.tensorObj G).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  inferInstanceAs ((IsGrothendieckAbelian.tensorObj G).mapDerivedCategory.CommShift ℤ)

/-- The functor induced by the Gabriel--Popescu left adjoint is exact. -/
instance derivedTensorObj_isTriangulated (G : C) (hG : IsSeparator G) :
    (derivedTensorObj G hG).IsTriangulated :=
  letI : PreservesFiniteLimits (IsGrothendieckAbelian.tensorObj G) :=
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits G hG
  letI : PreservesBinaryBiproducts (IsGrothendieckAbelian.tensorObj G) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  letI : (IsGrothendieckAbelian.tensorObj G).Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  inferInstanceAs ((IsGrothendieckAbelian.tensorObj G).mapDerivedCategory.IsTriangulated)

/-- The derived Gabriel--Popescu situation attached to a separator `G` of a Grothendieck
abelian category `C`.

The field `comparison` exhibits `rightDerived` as the right derived functor of the
Gabriel--Popescu embedding `Hom(G, -)`. The left adjoint is not an arbitrary left derived
functor but the functor on derived categories induced by the exact functor `- ⊗ G`, and
`counitIsIso` is the derived form of the identity `(- ⊗ G) ∘ Hom(G, -) = id`. -/
structure DerivedGabrielPopescuData (G : C) (hG : IsSeparator G) where
  /-- The right derived functor of the Gabriel--Popescu embedding. -/
  rightDerived : DerivedCategory C ⥤
    DerivedCategory (ModuleCat.{v} (End G)ᵐᵒᵖ)
  /-- The canonical comparison from the underived functor to its right
  derived functor. -/
  comparison :
    (preadditiveCoyonedaObj G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ rightDerived
  /-- The comparison map makes `rightDerived` a right derived functor. -/
  isRightDerived : rightDerived.IsRightDerivedFunctor comparison
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  /-- The derived tensor functor is left adjoint to the derived embedding. -/
  adjunction : derivedTensorObj G hG ⊣ rightDerived
  /-- The right derived embedding is fully faithful. -/
  fullyFaithful : rightDerived.FullyFaithful
  /-- The canonical counit identifies `F ∘ RG` with the identity functor. -/
  counitIsIso : IsIso adjunction.counit

/-- **Stacks 0F5V (Gabriel--Popescu on derived categories).** The
Gabriel--Popescu embedding of a Grothendieck abelian category admits a fully
faithful right derived functor.  Its left adjoint is induced by the exact
Gabriel--Popescu left adjoint, and the counit is an isomorphism. -/
@[stacks 0F5V]
theorem exists_derivedGabrielPopescuData (G : C) (hG : IsSeparator G) :
    Nonempty (DerivedGabrielPopescuData G hG) := by
  classical
  let L : ModuleCat.{v} (End G)ᵐᵒᵖ ⥤ C := IsGrothendieckAbelian.tensorObj G
  let R : C ⥤ ModuleCat.{v} (End G)ᵐᵒᵖ := preadditiveCoyonedaObj G
  let adj : L ⊣ R := IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction G
  let : R.Full := IsGrothendieckAbelian.GabrielPopescu.full G hG
  let : R.Faithful := (isSeparator_iff_faithful_preadditiveCoyonedaObj G).1 hG
  let : PreservesFiniteLimits L :=
    IsGrothendieckAbelian.GabrielPopescu.preservesFiniteLimits G hG
  let : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  let : L.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let W := HomotopyCategory.quasiIso C (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := C)
  let Q' := DerivedCategory.Qh (C := ModuleCat.{v} (End G)ᵐᵒᵖ)
  let F := R.mapHomotopyCategory (ComplexShape.up ℤ)
  have hPoint :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (F ⋙ Q') fun K => ⟨_, _, kInjectiveResolutionFunctor_obj_isKInjective C K,
        kInjectiveResolutionInclusion_quasiIso C K⟩
  let : (F ⋙ Q').HasPointwiseRightDerivedFunctor W := hPoint.1
  let RF := (F ⋙ Q').totalRightDerived Q W
  let β := (F ⋙ Q').totalRightDerivedUnit Q W
  let : RF.IsRightDerivedFunctor β W := by
    dsimp [RF, β, F, Q, W, Q']
    infer_instance
  have hres : ∀ K : CochainComplex C ℤ, W ((HomotopyCategory.quotient C (.up ℤ)).map
      ((kInjectiveResolutionInclusion C).app K)) := fun K =>
    (HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      (kInjectiveResolutionInclusion_quasiIso C K)
  have hRF : ∀ (F₀ : HomotopyCategory C (ComplexShape.up ℤ) ⥤
        DerivedCategory (ModuleCat.{v} (End G)ᵐᵒᵖ))
      (RF₀ : DerivedCategory C ⥤ DerivedCategory (ModuleCat.{v} (End G)ᵐᵒᵖ))
      (β₀ : F₀ ⟶ DerivedCategory.Qh ⋙ RF₀),
      (∀ I : CochainComplex C ℤ, I.IsKInjective →
        IsIso (β₀.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))) →
      ∀ K : HomotopyCategory C (ComplexShape.up ℤ),
      ∃ (c : Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) ⊤ K ⋙ Under.forget K ⋙ F₀)),
        ∃ (_ : F₀.IsRightDerivedValueAt (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) K c),
          ∃ (e : c.pt ≅ RF₀.obj (DerivedCategory.Qh.obj K)),
            ∀ s : (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)).Under ⊤ K,
              c.ι.app s ≫ e.hom ≫ RF₀.map (DerivedCategory.Qh.map s.hom) = β₀.app s.right := by
    intro F₀ RF₀ β₀ hβ K
    obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    have hI := kInjectiveResolutionFunctor_obj_isKInjective C Kc
    let qh := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((kInjectiveResolutionInclusion C).app Kc)
    let t₀ := MorphismProperty.Under.mk ⊤ qh (hres Kc)
    let ht := isTerminalUnderKInjective ((kInjectiveResolutionFunctor C).obj Kc) qh (hres Kc)
    have : IsIso (β₀.app t₀.right) := hβ _ hI
    have := Localization.inverts Q W _ t₀.prop
    let eβ := asIso (β₀.app t₀.right)
    let eRF := asIso (RF₀.map (DerivedCategory.Qh.map t₀.hom))
    refine ⟨_, coconeOfTerminalUnder_isRightDerivedValueAt F₀ _ _ t₀ ht, eβ ≪≫ eRF.symm,
      fun s => ?_⟩
    have := Localization.inverts Q W _ s.prop
    have hComp : RF₀.map (DerivedCategory.Qh.map s.hom) ≫
        RF₀.map (DerivedCategory.Qh.map (ht.from s).right) = eRF.hom := by
      rw [← Functor.map_comp, ← Functor.map_comp, MorphismProperty.Under.w (ht.from s)]
      rfl
    have hcancel : RF₀.map (DerivedCategory.Qh.map (ht.from s).right) ≫ eRF.inv ≫
        RF₀.map (DerivedCategory.Qh.map s.hom) = 𝟙 _ := by
      rw [← cancel_epi (RF₀.map (DerivedCategory.Qh.map s.hom)), reassoc_of% hComp]
      exact (eRF.hom_inv_id_assoc _).trans (Category.comp_id _).symm
    have hnat : F₀.map (ht.from s).right ≫ eβ.hom =
        β₀.app s.right ≫ RF₀.map (DerivedCategory.Qh.map (ht.from s).right) :=
      β₀.naturality _
    dsimp [Limits.coconeOfDiagramTerminal]
    rw [Category.assoc, reassoc_of% hnat, hcancel, Category.comp_id]
  have hLG : ∀ N : HomotopyCategory (ModuleCat.{v} (End G)ᵐᵒᵖ) (ComplexShape.up ℤ),
      ∃ (d : Cone (MorphismProperty.Over.forget
          (HomotopyCategory.quasiIso (ModuleCat.{v} (End G)ᵐᵒᵖ) (ComplexShape.up ℤ)) ⊤ N ⋙
            Over.forget N ⋙ L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)),
        ∃ (_ : (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh).IsLeftDerivedValueAt
            (HomotopyCategory.quasiIso (ModuleCat.{v} (End G)ᵐᵒᵖ) (ComplexShape.up ℤ)) N d),
          ∃ (e : L.mapDerivedCategory.obj (DerivedCategory.Qh.obj N) ≅ d.pt),
            ∀ t : (HomotopyCategory.quasiIso (ModuleCat.{v} (End G)ᵐᵒᵖ)
                (ComplexShape.up ℤ)).Over ⊤ N,
              L.mapDerivedCategory.map (DerivedCategory.Qh.map t.hom) ≫ e.hom ≫ d.π.app t =
                L.mapDerivedCategoryFactorsh.hom.app t.left := by
    intro N
    have hInv : (HomotopyCategory.quasiIso (ModuleCat.{v} (End G)ᵐᵒᵖ)
        (ComplexShape.up ℤ)).IsInvertedBy
        (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
      Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso L
    refine ⟨_, coneOfInvertedMorphisms_isLeftDerivedValueAt _ _ hInv N,
      L.mapDerivedCategoryFactorsh.app N, fun t => ?_⟩
    have : IsIso ((L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map t.hom) :=
      hInv t.hom t.prop
    have hn : L.mapDerivedCategory.map (DerivedCategory.Qh.map t.hom) ≫
        L.mapDerivedCategoryFactorsh.hom.app N = L.mapDerivedCategoryFactorsh.hom.app t.left ≫
          (L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map t.hom := by
      simpa using L.mapDerivedCategoryFactorsh.hom.naturality t.hom
    show _ ≫ L.mapDerivedCategoryFactorsh.hom.app N ≫
      inv ((L.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map t.hom) = _
    rw [reassoc_of% hn, ← Functor.comp_map, IsIso.hom_inv_id, Category.comp_id]
  have hkinj : ∀ {F₁ F₂ : DerivedCategory C ⥤ DerivedCategory C} (τ : F₁ ⟶ F₂),
      (∀ I : CochainComplex C ℤ, I.IsKInjective →
        IsIso (τ.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)))) → IsIso τ := by
    intro F₁ F₂ τ hτ
    suffices ∀ Y, IsIso (τ.app Y) from NatIso.isIso_of_isIso_app τ
    intro Y
    obtain ⟨K, hK⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage Y)
    let f : DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((kInjectiveResolutionFunctor C).obj K)) :=
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
        ((kInjectiveResolutionInclusion C).app K))
    have : IsIso f := Localization.inverts Q W _ (hres K)
    rw [← NatTrans.isIso_app_iff_of_iso τ (DerivedCategory.Qh.objObjPreimageIso Y), ← hK,
      NatTrans.isIso_app_iff_of_iso τ (asIso f)]
    exact hτ _ (kInjectiveResolutionFunctor_obj_isKInjective C K)
  obtain ⟨adjDerived, _, hCounitCompat⟩ :=
    CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      (homotopyAdjunction adj) W _ Q Q' RF β L.mapDerivedCategory
      L.mapDerivedCategoryFactorsh.hom
      (hRF _ RF β (hPoint.2 Q RF β)) hLG
  have hc : IsIso adjDerived.counit := hkinj _ fun I hI => by
    have : IsIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) :=
      HomologicalComplex.Hom.isIso_of_components _
    have : IsIso ((homotopyAdjunction adj).counit.app
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) := by
      rw [homotopyAdjunction_counit_app]
      exact ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).mapIso
        (asIso ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I))).isIso_hom
    have := hPoint.2 Q RF β I hI
    have : IsIso (L.mapDerivedCategory.map
        (β.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I)) ≫
          adjDerived.counit.app (Q.obj
            ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))) := by
      rw [hCounitCompat]
      infer_instance
    exact IsIso.of_isIso_comp_left (L.mapDerivedCategory.map
      (β.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj I))) _
  exact ⟨{
    rightDerived := RF
    comparison := β
    isRightDerived := inferInstance
    adjunction := adjDerived
    fullyFaithful := @Adjunction.fullyFaithfulROfIsIsoCounit _ _ _ _ _ _ adjDerived hc
    counitIsIso := hc }⟩

end Stacks.Injectives
