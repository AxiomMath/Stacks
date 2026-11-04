module

public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraMapLocallySurjective
public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonArrow
public import StacksFrontier.Deformation.AlgebraExtension.ConormalExtClass
public import StacksFrontier.Deformation.AlgebraExtension.PushoutFullyFaithful

/-!
# Pushout of extensions along a map of modules: essential surjectivity

Let `a : 𝒜 ⟶ 𝒪` be a morphism of sheaves of commutative rings on a small site and let
`φ : ℳ ⟶ 𝒩` be a morphism of `𝒪`-modules inducing a surjection
`Ext¹(NL_{𝒪/𝒜}, ℳ) ⟶ Ext¹(NL_{𝒪/𝒜}, 𝒩)`. Then every extension `Q` of `𝒜`-algebras of `𝒪` by
`𝒩` is the pushout along `φ` of an extension by `ℳ`; this is the essential surjectivity in
[Stacks Project, Tag 0D3P], which the source deduces from [Stacks Project, Tag 08UK].

The argument: present `Q` by the generators `ℰ_Q = 𝒪'_Q`, so that `Q` has a class `c` in
`Ext¹(NL_{𝒪/𝒜}, 𝒩)`, the class of its conormal map. Lift `-c` to a class `ζ` with values in
`ℳ`; by [Stacks Project, Tag 08UJ] there is a presentation `α'` on which `ζ` is the class of a
morphism `δ' : ℐ'/ℐ'² ⟶ ℳ`, and the square-zero pushout `P` of `𝒜[ℰ']` along `δ'` is an
extension by `ℳ` with conormal map `δ'`. On the generators `ℰ' ×_𝒪 ℰ_Q`, which lift to both `P`
and `Q`, the conormal maps of `P` (pushed along `φ`) and of `Q` have the same class, so they
differ by `θ ∘ d`; shifting the lift to `Q` by `θ` and applying Step 3 of
[Stacks Project, Tag 08UG] gives a morphism `P ⟶ Q` along `φ`, hence `F(P) ≅ Q`.

## Main definitions

* `Deformation.AlgebraExtension.GeneratorLift.precomp`: a lift precomposed with a morphism of
  presentations.
* `Deformation.AlgebraExtension.conormalPushout`: the square-zero pushout of `𝒜[ℰ]` along a
  morphism `δ : ℐ/ℐ² ⟶ ℳ`, with its canonical lift `conormalPushoutLift`.
* `Deformation.AlgebraExtension.fibrePresentation`: the generators `ℰ₁ ×_𝒪 ℰ₂`.

## Main results

* `Deformation.AlgebraExtension.GeneratorLift.conormalHom_precomp`
* `Deformation.AlgebraExtension.conormalHom_conormalPushoutLift`
* `Deformation.AlgebraExtension.IsPushoutFunctor.essSurj`

## References

* [Stacks Project, Tag 0D3P](https://stacks.math.columbia.edu/tag/0D3P)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UJ](https://stacks.math.columbia.edu/tag/08UJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.Differentials (underlyingRingSheaf)
open Stacks.Sites.Conormal (kernelIdeal)
open Stacks.Sites.FreeAlgebra
open Stacks.SheafOfModules (presentation presentationConormalSequence naiveCotangentComplex
  presentationConormalMap freeAlgebraMap)

universe t u

namespace Deformation.AlgebraExtension

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasWeakSheafify J CommRingCat.{u}]
  {A O : Sheaf J CommRingCat.{u}} {a : A ⟶ O}
  {M N : SheafOfModules.{u} (underlyingRingSheaf O)}

/-! ### Precomposing a lift with a morphism of presentations -/

section Precomp

variable {E₁ E₂ : Cᵒᵖ ⥤ Type u} (h : E₁ ⟶ E₂) {α₁ : E₁ ⟶ underlyingPresheaf J O}
  {α₂ : E₂ ⟶ underlyingPresheaf J O} (hα : h ≫ α₂ = α₁) {P : AlgebraExtension a M}

namespace GeneratorLift

/-- A lift of `α₂` precomposed with a morphism of presentations `h : ℰ₁ ⟶ ℰ₂`, as a lift
of `α₁`. -/
def precomp (β : GeneratorLift α₂ P) : GeneratorLift α₁ P where
  lift := h ≫ β.lift
  lift_comp := by rw [Category.assoc, β.lift_comp, hα]

/-- The algebra map of a precomposed lift is the renaming `𝒜[ℰ₁] ⟶ 𝒜[ℰ₂]` along `h` followed by
the algebra map of the original lift. -/
theorem precomp_hom (β : GeneratorLift α₂ P) :
    (β.precomp h hα).hom = freeAlgebraMap J A E₁ E₂ h ≫ β.hom := by
  refine freeAlgebraSheaf_hom_ext J A P.extension E₁ ?_ ?_
  · rw [coefficientMap_hom, ← Category.assoc,
      Stacks.SheafOfModules.freeAlgebraSheafCoefficientMap_comp_freeAlgebraMap,
      coefficientMap_hom]
  · rw [variable_hom, CategoryTheory.Functor.map_comp, Functor.whiskerRight_comp,
      ← Category.assoc, Stacks.SheafOfModules.freeAlgebraSheafVariable_comp_freeAlgebraMap,
      Category.assoc, variable_hom]
    rfl

variable [Presheaf.IsLocallySurjective J (presentation J A O a E₁ α₁).hom]
  [Presheaf.IsLocallySurjective J (presentation J A O a E₂ α₂).hom]

/-- **The conormal map of a precomposed lift** is the conormal map of the lift precomposed
with the induced map of conormal sheaves. -/
theorem conormalHom_precomp (β : GeneratorLift α₂ P) :
    (β.precomp h hα).conormalHom =
      presentationConormalMap.{u, u, u, u} J A E₁ E₂ h O a α₁ α₂ hα ≫ β.conormalHom :=
  conormal_ext fun U g => by
    rw [conormalHom_relClass]
    refine Eq.trans ?_ (congrArg (β.conormalHom.val.app U)
      (Stacks.Sites.Conormal.conormalSheafMapOfFac_conormalClass.{u, u, u, u} (J := J) (R := A)
        (φ₁ := presentation J A O a E₁ α₁) (φ₂ := presentation J A O a E₂ α₂)
        (ψ := freeAlgebraMap J A E₁ E₂ h)
        (hψ := Stacks.SheafOfModules.freeAlgebraMap_comp_presentation J A E₁ E₂ h O a α₁ α₂ hα)
        (a₁ := freeAlgebraSheafCoefficientMap J A E₁)
        (a₂ := freeAlgebraSheafCoefficientMap J A E₂) (X := U) (x := g))).symm
    rw [conormalHom_relClass]
    refine P.incl_injective ?_
    rw [incl_restriction, incl_restriction, precomp_hom]
    rfl

end GeneratorLift

end Precomp

/-! ### The square-zero pushout along a conormal map -/

section ConormalPushout

variable {E : Cᵒᵖ ⥤ Type u} {α : E ⟶ underlyingPresheaf J O}
  [Presheaf.IsLocallySurjective J (presentation J A O a E α).hom]
  (δ : (presentationConormalSequence.{u, u, u, u} J A O a E α).X₁ ⟶ tensorModule M)

/-- The pushout data of a morphism `δ : ℐ/ℐ² ⟶ ℳ`: the presentation `𝒜[ℰ] ⟶ 𝒪` with the
map `g ↦ δ(ḡ)` on its relations. -/
noncomputable def conormalPushout : PresentationPushout a M where
  presentation := freeAlgebraSheaf J A E
  proj := presentation J A O a E α
  locallySurjective := inferInstance
  base := freeAlgebraSheafCoefficientMap J A E
  base_proj := freeAlgebraSheafCoefficientMap_comp_desc J A O E a α
  psi :=
    { app := fun U => AddMonoidHom.mk' (fun g => δ.val.app U (GeneratorLift.relClass U g))
        fun g g' => by
          change δ.val.app U (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} J A _ O _ _ U
            (g + g')) = _
          rw [Stacks.Sites.Conormal.conormalClass_add, map_add]
          rfl
      app_smul := fun U r g => by
        change δ.val.app U (Stacks.Sites.Conormal.conormalClass.{u, u, u, u} J A _ O _ _ U
          (r • g)) = _
        rw [Stacks.Sites.Conormal.conormalClass_smul, map_smul]
        rfl
      app_map := fun {U V} f g =>
        (congrArg (δ.val.app V) (Stacks.Sites.Conormal.conormalClass_map.{u, u, u, u} J A _ O _ _
          f g _ rfl)).trans (PresheafOfModules.naturality_apply δ.val f _)
      smul_eq_zero := fun U g m => by
        have h : (show (underlyingRingSheaf O).obj.obj U from
            (presentation J A O a E α).hom.app U (g : (freeAlgebraSheaf J A E).obj.obj U)) = 0 :=
          RingHom.mem_ker.1 g.2
        have h2 : (show (underlyingRingSheaf O).obj.obj U from
              (presentation J A O a E α).hom.app U (g : (freeAlgebraSheaf J A E).obj.obj U)) •
            (show M.val.obj U from m) = 0 := by
          rw [h, zero_smul]
        exact h2 }

variable [J.WEqualsLocallyBijective CommRingCat.{u}]

/-- The canonical lift of the generators to the pushout along `δ`. -/
noncomputable def conormalPushoutLift : GeneratorLift α (conormalPushout δ).extension where
  lift := freeAlgebraSheafVariable J A E ≫ Functor.whiskerRight
    ((sheafToPresheaf J CommRingCat.{u}).map (conormalPushout δ).lift) (forget CommRingCat.{u})
  lift_comp := by
    have h1 : Functor.whiskerRight (conormalPushout δ).lift.hom (forget CommRingCat.{u}) ≫
        Functor.whiskerRight (conormalPushout δ).extension.reduction.hom (forget CommRingCat.{u}) =
          Functor.whiskerRight (presentation J A O a E α).hom (forget CommRingCat.{u}) := by
      rw [← Functor.whiskerRight_comp]
      exact congrArg (fun t => Functor.whiskerRight t.hom (forget CommRingCat.{u}))
        (conormalPushout δ).lift_reduction
    exact (Category.assoc _ _ _).trans ((congrArg (freeAlgebraSheafVariable J A E ≫ ·) h1).trans
      (freeAlgebraSheafVariable_comp_desc J A O E a α))

/-- The algebra map of the canonical lift is the lift of the pushout along `δ`. -/
theorem conormalPushoutLift_hom : (conormalPushoutLift δ).hom = (conormalPushout δ).lift :=
  freeAlgebraSheaf_hom_ext J A _ E ((conormalPushoutLift δ).coefficientMap_hom.trans
    (conormalPushout δ).base_lift.symm) (conormalPushoutLift δ).variable_hom

/-- **The conormal map of the pushout along `δ` is `δ`.** -/
theorem conormalHom_conormalPushoutLift : (conormalPushoutLift δ).conormalHom = δ :=
  GeneratorLift.conormal_ext fun U g => by
    rw [GeneratorLift.conormalHom_relClass]
    refine (conormalPushout δ).extension.incl_injective ?_
    rw [GeneratorLift.incl_restriction, conormalPushoutLift_hom]
    exact (conormalPushout δ).lift_app_kernel U g

end ConormalPushout

/-! ### The generators `ℰ₁ ×_𝒪 ℰ₂` -/

section FibrePresentation

variable {E₁ E₂ : Cᵒᵖ ⥤ Type u} (α₁ : E₁ ⟶ underlyingPresheaf J O)
  (α₂ : E₂ ⟶ underlyingPresheaf J O)

/-- The fibre product `ℰ₁ ×_𝒪 ℰ₂` of two families of generators. -/
noncomputable def fibrePresentation : Cᵒᵖ ⥤ Type u where
  obj U := {p : E₁.obj U × E₂.obj U // α₁.app U p.1 = α₂.app U p.2}
  map {U V} f := TypeCat.ofHom fun p => ⟨(E₁.map f p.1.1, E₂.map f p.1.2), by
    rw [NatTrans.naturality_apply α₁ f, NatTrans.naturality_apply α₂ f, p.2]⟩
  map_id U := by
    ext p
    · change E₁.map (𝟙 U) p.1.1 = p.1.1
      rw [CategoryTheory.Functor.map_id]
      rfl
    · change E₂.map (𝟙 U) p.1.2 = p.1.2
      rw [CategoryTheory.Functor.map_id]
      rfl
  map_comp f g := by
    ext p
    · change E₁.map (f ≫ g) p.1.1 = _
      rw [CategoryTheory.Functor.map_comp]
      rfl
    · change E₂.map (f ≫ g) p.1.2 = _
      rw [CategoryTheory.Functor.map_comp]
      rfl

/-- The first projection of `ℰ₁ ×_𝒪 ℰ₂`. -/
noncomputable def fibrePresentationFst : fibrePresentation α₁ α₂ ⟶ E₁ where
  app _ := TypeCat.ofHom fun p => p.1.1
  naturality _ _ _ := rfl

/-- The second projection of `ℰ₁ ×_𝒪 ℰ₂`. -/
noncomputable def fibrePresentationSnd : fibrePresentation α₁ α₂ ⟶ E₂ where
  app _ := TypeCat.ofHom fun p => p.1.2
  naturality _ _ _ := rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J CommRingCat] in
/-- The two projections of `ℰ₁ ×_𝒪 ℰ₂` agree after composing with `α₂` and `α₁`. -/
theorem fibrePresentation_condition :
    fibrePresentationSnd α₁ α₂ ≫ α₂ = fibrePresentationFst α₁ α₂ ≫ α₁ := by
  ext U p
  exact p.2.symm

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] [HasWeakSheafify J CommRingCat] in
/-- The first projection is locally surjective when `α₂` is. -/
theorem isLocallySurjective_fibrePresentationFst [Presheaf.IsLocallySurjective J α₂] :
    Presheaf.IsLocallySurjective J (fibrePresentationFst α₁ α₂) := ⟨fun {U} x => by
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J α₂ (α₁.app (op U) x))
  rintro Y f ⟨y, hy⟩
  exact ⟨⟨(E₁.map f.op x, y), (NatTrans.naturality_apply α₁ f.op x).trans hy.symm⟩, rfl⟩⟩

end FibrePresentation

/-- The comparison class of a presentation pulled back along a morphism of presentations
`h` is the two-term class of the pulled-back conormal map. -/
private theorem comparison_comp_eq_conormalExtClass
    [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
    {E₁ E₂ : Cᵒᵖ ⥤ Type u} (h : E₁ ⟶ E₂) {α₁ : E₁ ⟶ underlyingPresheaf J O}
    {α₂ : E₂ ⟶ underlyingPresheaf J O}
    (hα : h ≫ α₂ = α₁) [Presheaf.IsLocallySurjective J (presentation J A O a E₁ α₁).hom]
    [Presheaf.IsLocallySurjective J (presentation J A O a E₂ α₂).hom]
    {G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    (ξ : DerivedCategory.Q.obj (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj G)⟦(1 : ℤ)⟧)
    (δ : (presentationConormalSequence.{u, u, u, u} J A O a E₂ α₂).X₁ ⟶ G)
    (hξ : DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
        J A O a E₂ α₂) ≫ ξ = (presentationTwoTerm a E₂ α₂).conormalExtClass G δ) :
    DerivedCategory.Q.map (Stacks.SheafOfModules.naiveCotangentComplexComparison.{u, u, u, u}
        J A O a E₁ α₁) ≫ ξ = (presentationTwoTerm a E₁ α₁).conormalExtClass G
        (presentationConormalMap.{u, u, u, u} J A E₁ E₂ h O a α₁ α₂ hα ≫ δ) := by
  rw [← conormalExtClass_naturality G h hα δ, ← hξ, ← Category.assoc, ← Functor.map_comp,
    Stacks.SheafOfModules.naiveCotangentComplexComparison_naturality]

/-! ### Essential surjectivity -/

section EssSurj

variable [J.WEqualsLocallyBijective CommRingCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [J.HasSheafCompose (forget CommRingCat.{u})]
  [(forget CommRingCat.{u}).ReflectsIsomorphisms]
  [HasDerivedCategory.{t} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  {φ : M ⟶ N} {F : AlgebraExtension a M ⥤ AlgebraExtension a N}

/-- **Pushout along `φ` is essentially surjective** as soon as `φ` induces a surjection on
`Ext¹(NL_{𝒪/𝒜}, −)`. -/
theorem IsPushoutFunctor.essSurj (hF : IsPushoutFunctor φ F)
    (h1 : Function.Surjective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj
          (tensorModule M))⟦(1 : ℤ)⟧ =>
      ξ ≫ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map
          (tensorMap φ))⟦(1 : ℤ)⟧')) :
    F.EssSurj where
  mem_essImage Q := by
    have := isLocallySurjective_fibreMap Q Q
    let β₀ := fibreFst Q Q
    let ξ := (presentationTwoTermIso a (fibreGenerators Q Q) (fibreMap Q Q)).inv ≫
      (presentationTwoTerm a (fibreGenerators Q Q) (fibreMap Q Q)).conormalExtClass _
        β₀.conormalHom
    obtain ⟨η, hη⟩ := h1 ξ
    obtain ⟨E₁, α₁, hs₁, f₁, hf₁⟩ :=
      Stacks.SheafOfModules.exists_presentation_conormalExtClass.{u, u, u, t} J A O a
        (tensorModule M) η
    have := hs₁
    have := isLocallySurjective_fibrePresentationFst (J := J) α₁ (fibreMap Q Q)
    have : Presheaf.IsLocallySurjective J (presentation J A O a
        (fibrePresentation α₁ (fibreMap Q Q)) (fibrePresentationFst α₁ (fibreMap Q Q) ≫ α₁)).hom :=
      Stacks.Sites.FreeAlgebra.isLocallySurjective_presentation_comp J A _ _ a α₁
    have hα₀ : fibrePresentationSnd α₁ (fibreMap Q Q) ≫ fibreMap Q Q =
        fibrePresentationFst α₁ (fibreMap Q Q) ≫ α₁ := fibrePresentation_condition _ _
    let β₂ := β₀.precomp (fibrePresentationSnd α₁ (fibreMap Q Q)) hα₀
    let ψ := presentationConormalMap.{u, u, u, u} J A _ E₁.obj
      (fibrePresentationFst α₁ (fibreMap Q Q)) O a _ α₁ rfl ≫ (-f₁)
    -- the classes of `β₂` and of `ψ` pushed along `φ` agree
    let T₀ := presentationTwoTerm a (fibreGenerators Q Q) (fibreMap Q Q)
    let T₁ := presentationTwoTerm a E₁.obj α₁
    let T₂ := presentationTwoTerm a (fibrePresentation α₁ (fibreMap Q Q))
      (fibrePresentationFst α₁ (fibreMap Q Q) ≫ α₁)
    have e1 : T₂.conormalExtClass _ β₂.conormalHom = _ ≫ ξ :=
      (congrArg (T₂.conormalExtClass _) (GeneratorLift.conormalHom_precomp _ hα₀ β₀)).trans
        (comparison_comp_eq_conormalExtClass (fibrePresentationSnd α₁ (fibreMap Q Q)) hα₀ ξ _
          (Iso.hom_inv_id_assoc (presentationTwoTermIso a (fibreGenerators Q Q)
            (fibreMap Q Q)) _)).symm
    have e2 := comparison_comp_eq_conormalExtClass (fibrePresentationFst α₁ (fibreMap Q Q))
      (rfl : _ ≫ α₁ = _) η (-f₁) (hf₁.trans ((presentationConormalExtClass_eq_neg _ f₁).trans
        (conormalExtClass_neg _ f₁).symm))
    have hc : T₂.conormalExtClass _ (ψ ≫ tensorMap φ) = T₂.conormalExtClass _ β₂.conormalHom :=
      (conormalExtClass_comp _ ψ (tensorMap φ)).symm.trans
        ((congrArg (· ≫ _) e2.symm).trans
          ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hη).trans e1.symm)))
    obtain ⟨θ, hθ⟩ := exists_d_comp_eq_sub_of_conormalExtClass_eq _ hc
    -- the pushout along `-ψ`, and a morphism from it to `Q` along `φ`
    let βP := conormalPushoutLift (M := M) ψ
    have hβ' : (β₂.shift θ).conormalHom = βP.conormalHom ≫ tensorMap φ := by
      rw [GeneratorLift.conormalHom_shift, hθ, conormalHom_conormalPushoutLift]
      exact add_sub_cancel _ _
    obtain ⟨k, -⟩ := GeneratorLift.exists_mapAlong_comp_eq βP (β₂.shift θ) fun U g =>
      ((β₂.shift θ).conormalHom_relClass U g).symm.trans
        ((congrArg (fun f => f.val.app U (GeneratorLift.relClass U g)) hβ').trans
          (congrArg (φ.val.app U) (βP.conormalHom_relClass U g)))
    obtain ⟨g, -, -⟩ := hF.desc_unique _ Q k
    exact ⟨_, ⟨asIso g⟩⟩

/-- **Pushout along `φ` is an equivalence of categories** of extensions of `𝒜`-algebras of `𝒪`
as soon as `φ` induces bijections `Ext^i(NL_{𝒪/𝒜}, ℳ) ⟶ Ext^i(NL_{𝒪/𝒜}, 𝒩)` for `i = 0, 1`:
the site-level form of [Stacks Project, Tag 0D3P]. -/
theorem IsPushoutFunctor.isEquivalence (hF : IsPushoutFunctor φ F)
    (h0 : Function.Bijective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj (tensorModule M) =>
      ξ ≫ (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map (tensorMap φ)))
    (h1 : Function.Bijective (fun ξ : DerivedCategory.Q.obj
        (naiveCotangentComplex.{u, u, u, u} J A O a) ⟶ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).obj
          (tensorModule M))⟦(1 : ℤ)⟧ =>
      ξ ≫ ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) 0).map
          (tensorMap φ))⟦(1 : ℤ)⟧')) :
    F.IsEquivalence :=
  have := hF.faithful h0.1
  have := hF.full h0.2 h1.1
  have := hF.essSurj h1.2
  { }

end EssSurj

end Deformation.AlgebraExtension

end
