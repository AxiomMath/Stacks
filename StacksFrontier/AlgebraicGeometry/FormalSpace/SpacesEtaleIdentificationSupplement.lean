module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleIdentification
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSectionsAlongThickening
public import StacksFrontier.AlgebraicGeometry.FormalSpace.GeneralReduction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Full faithfulness of the comparison functor for étale formal algebraic spaces

Let `X` be a formal algebraic space with reduction `X_red`. A morphism into an fppf sheaf that is
representable by algebraic spaces and étale over `Y`, prescribed along a representable thickening
of its source, extends uniquely. Applied to the thickening `U_red ⟶ U`, this shows that the
comparison functor from formal algebraic spaces representable étale over `X` to those over
`X_red` is fully faithful.

## Main definitions

* `objReduction'`: The reduction of a formal algebraic space representable étale over `X`.

## Main results

* `existsUnique_hom_of_isRepresentableThickening`: A morphism into a sheaf representable étale
  over `Y`, given along a representable thickening of its source, extends uniquely.
* `bijective_spacesEtaleComparison_map`: The comparison functor is bijective on morphisms.
* `faithful_spacesEtaleComparison`: The comparison functor is faithful.
* `full_spacesEtaleComparison`: The comparison functor is full.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {B S hS}

/-! ### Lifting a morphism along a representable thickening against a representable étale target -/

/-- `AlgebraicGeometry.FormalSpace.existsUnique_section_uliftYoneda_of_isThickening` with the
universe lift of the Yoneda presheaf of `T` spelled `uliftYoneda.obj T` throughout rather than
`yoneda.obj T ⋙ uliftFunctor`. The two are definitionally equal, but only the former spelling
lets the associativity of composition be rewritten in the lifts below, since a rewrite has to
match the object of the site-level composite syntactically. -/
private theorem existsUnique_section_of_isThickening_uliftYoneda
    {T₀ T : BigFppfOver B S hS} (k : T₀ ⟶ T)
    (hk : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map k))
    {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (hP : Space.IsAlgebraicSpaceULift.{u + 1} B S hS P)
    (pr : P ⟶ (uliftYoneda.{u + 1}).obj T)
    (hpr : Space.IsEtaleULift.{u + 1} B S hS pr)
    (σ₀ : (uliftYoneda.{u + 1}).obj T₀ ⟶ P)
    (hσ₀ : σ₀ ≫ pr = (uliftYoneda.{u + 1}).map k) :
    ∃! σ : (uliftYoneda.{u + 1}).obj T ⟶ P,
      σ ≫ pr = 𝟙 ((uliftYoneda.{u + 1}).obj T) ∧ (uliftYoneda.{u + 1}).map k ≫ σ = σ₀ :=
  existsUnique_section_uliftYoneda_of_isThickening B S hS k hk hP pr hpr σ₀ hσ₀

/-- The scheme-valued form of
`AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening`: over an object
`T` of the site, a morphism `x : T ⟶ Z` and a morphism `T ×_Z Z₀ ⟶ A` over `Y` determine a
unique morphism `T ⟶ A` over `Y` restricting to it.

The base change of the thickening along `x` is the one the representability of `ι` chooses, so
nothing is quantified over here and the lift is a function of `x`; that is what makes the
pointwise lifts of the theorem below natural in `T`. -/
private theorem existsUnique_uliftYonedaHom_of_isRepresentableThickening
    {Y Z Z₀ A : FppfSheaf B S hS} {ι : Z₀ ⟶ Z}
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    {q : A ⟶ Y} (hq : IsRepresentableEtale B S hS q) (z : Z ⟶ Y)
    {h : Z₀ ⟶ A} (hh : h ≫ q = ι ≫ z)
    (T : BigFppfOver B S hS) (x : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj) :
    ∃! w : (uliftYoneda.{u + 1}).obj T ⟶ A.obj,
      w ≫ q.hom = x ≫ z.hom ∧
        (uliftYoneda.{u + 1}).map (hι.rep.snd x) ≫ w = hι.rep.fst x ≫ h.hom := by
  have hcomp : h.hom ≫ q.hom = ι.hom ≫ z.hom := congrArg (fun k : Z₀ ⟶ Y ↦ k.hom) hh
  have hsq : (uliftYoneda.{u + 1}).map (hι.rep.snd x) ≫ (x ≫ z.hom)
      = (hι.rep.fst x ≫ h.hom) ≫ q.hom := by
    rw [← Category.assoc, ← (hι.rep.isPullback x).w, Category.assoc, ← hcomp, Category.assoc]
  have hlf : pullback.lift ((uliftYoneda.{u + 1}).map (hι.rep.snd x))
        (hι.rep.fst x ≫ h.hom) hsq ≫ pullback.fst (x ≫ z.hom) q.hom
      = (uliftYoneda.{u + 1}).map (hι.rep.snd x) := pullback.lift_fst _ _ _
  have hls : pullback.lift ((uliftYoneda.{u + 1}).map (hι.rep.snd x))
        (hι.rep.fst x ≫ h.hom) hsq ≫ pullback.snd (x ≫ z.hom) q.hom
      = hι.rep.fst x ≫ h.hom := pullback.lift_snd _ _ _
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, hσu⟩ :=
    existsUnique_section_of_isThickening_uliftYoneda (hι.rep.snd x)
      (hι.property_snd x) (hq.1 T (x ≫ z.hom)) (pullback.fst (x ≫ z.hom) q.hom)
      (hq.2 T (x ≫ z.hom)) _ hlf
  refine ⟨σ ≫ pullback.snd (x ≫ z.hom) q.hom, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hσ₁, Category.id_comp]
  · rw [← Category.assoc, hσ₂, hls]
  · rintro w ⟨hw₁, hw₂⟩
    have hcone : (𝟙 ((uliftYoneda.{u + 1}).obj T)) ≫ (x ≫ z.hom) = w ≫ q.hom := by
      rw [Category.id_comp, hw₁]
    have hlift : pullback.lift (𝟙 ((uliftYoneda.{u + 1}).obj T)) w hcone = σ := by
      refine hσu _ ⟨pullback.lift_fst _ _ _, pullback.hom_ext ?_ ?_⟩
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hlf]
      · rw [Category.assoc, pullback.lift_snd, hw₂, hls]
    rw [← hlift, pullback.lift_snd]

/-- A pointwise lift of
`AlgebraicGeometry.FormalSpace.existsUnique_uliftYonedaHom_of_isRepresentableThickening`
restricts along any cone over the base change of the thickening to the prescribed morphism. -/
private theorem comp_lift_eq_of_comp_eq_of_isRepresentableThickening
    {Y Z Z₀ A : FppfSheaf B S hS} {ι : Z₀ ⟶ Z}
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    {q : A ⟶ Y} (z : Z ⟶ Y) {h : Z₀ ⟶ A}
    {W : ∀ (T : BigFppfOver B S hS), ((uliftYoneda.{u + 1}).obj T ⟶ Z.obj) →
      ((uliftYoneda.{u + 1}).obj T ⟶ A.obj)}
    (hW : ∀ T x, W T x ≫ q.hom = x ≫ z.hom ∧
      (uliftYoneda.{u + 1}).map (hι.rep.snd x) ≫ W T x = hι.rep.fst x ≫ h.hom)
    {T : BigFppfOver B S hS} (x : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj)
    {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)} (a : E ⟶ Z₀.obj)
    (b : E ⟶ (uliftYoneda.{u + 1}).obj T) (hab : a ≫ ι.hom = b ≫ x) :
    b ≫ W T x = a ≫ h.hom := by
  have hl₁ := (hι.rep.isPullback x).lift_fst a b hab
  have hl₂ := (hι.rep.isPullback x).lift_snd a b hab
  rw [← hl₂, Category.assoc, (hW T x).2, ← Category.assoc, hl₁]

/-- The pointwise lifts of
`AlgebraicGeometry.FormalSpace.existsUnique_uliftYonedaHom_of_isRepresentableThickening` are
natural in `T`, by their uniqueness. -/
private theorem uliftYoneda_map_comp_lift_of_isRepresentableThickening
    {Y Z Z₀ A : FppfSheaf B S hS} {ι : Z₀ ⟶ Z}
    (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    {q : A ⟶ Y} (z : Z ⟶ Y) {h : Z₀ ⟶ A}
    (W : ∀ (T : BigFppfOver B S hS), ((uliftYoneda.{u + 1}).obj T ⟶ Z.obj) →
      ((uliftYoneda.{u + 1}).obj T ⟶ A.obj))
    (hW : ∀ T x, W T x ≫ q.hom = x ≫ z.hom ∧
      (uliftYoneda.{u + 1}).map (hι.rep.snd x) ≫ W T x = hι.rep.fst x ≫ h.hom)
    (hWu : ∀ T x (w : (uliftYoneda.{u + 1}).obj T ⟶ A.obj), (w ≫ q.hom = x ≫ z.hom ∧
      (uliftYoneda.{u + 1}).map (hι.rep.snd x) ≫ w = hι.rep.fst x ≫ h.hom) → w = W T x)
    (T T' : BigFppfOver B S hS) (g : T' ⟶ T) (x : (uliftYoneda.{u + 1}).obj T ⟶ Z.obj) :
    (uliftYoneda.{u + 1}).map g ≫ W T x = W T' ((uliftYoneda.{u + 1}).map g ≫ x) := by
  refine hWu T' _ _ ⟨?_, ?_⟩
  · rw [Category.assoc, (hW T x).1, ← Category.assoc]
  · rw [← Category.assoc]
    refine comp_lift_eq_of_comp_eq_of_isRepresentableThickening hι z hW x _ _ ?_
    rw [(hι.rep.isPullback ((uliftYoneda.{u + 1}).map g ≫ x)).w, Category.assoc]

/-- **A morphism into an fppf sheaf representable étale over `Y`, prescribed along a
representable thickening of its source, extends uniquely.** Let `ι : Z₀ ⟶ Z` be a representable
thickening of fppf sheaves — the inclusion of a reduction is one — and let `q : A ⟶ Y` be
representable by algebraic spaces and étale. Every morphism `Z₀ ⟶ A` over `Y` is the restriction
of a unique morphism `Z ⟶ A` over `Y`.

This is the sheaf-level form of the general-thickening half of Stacks 05ZH, and it is the whole
geometric content of the full faithfulness of the comparison functor of Stacks 0DEG. Over an
object `T` of the site it is
`AlgebraicGeometry.FormalSpace.existsUnique_section_uliftYoneda_of_isThickening`, applied to the
base change of `A` along the scheme-valued point of `Y` that `T` carries; those pointwise lifts
are natural in `T` by their own uniqueness, which is what assembles them into a morphism of
sheaves without any gluing. -/
@[ega "IV 18.1.3" "more general"]
theorem existsUnique_hom_of_isRepresentableThickening {Y Z Z₀ A : FppfSheaf B S hS}
    {ι : Z₀ ⟶ Z} (hι : Space.IsRepresentableThickeningULift.{u + 1} B S hS ι.hom)
    {q : A ⟶ Y} (hq : IsRepresentableEtale B S hS q) (z : Z ⟶ Y)
    {h : Z₀ ⟶ A} (hh : h ≫ q = ι ≫ z) :
    ∃! f : Z ⟶ A, f ≫ q = z ∧ ι ≫ f = h := by
  choose W hW hWu using
    existsUnique_uliftYonedaHom_of_isRepresentableThickening hι hq z hh
  have hnat := uliftYoneda_map_comp_lift_of_isRepresentableThickening hι z W hW hWu
  refine ⟨⟨{ app := fun T ↦ TypeCat.ofHom fun ξ ↦
               uliftYonedaEquiv.{u + 1} (W T.unop (uliftYonedaEquiv.{u + 1}.symm ξ))
             naturality := fun T T' g ↦ ConcreteCategory.hom_ext _ _ fun ξ ↦ ?_ }⟩,
    ⟨?_, ?_⟩, ?_⟩
  · show uliftYonedaEquiv.{u + 1}
        (W T'.unop (uliftYonedaEquiv.{u + 1}.symm (Z.obj.map g ξ)))
      = A.obj.map g (uliftYonedaEquiv.{u + 1} (W T.unop (uliftYonedaEquiv.{u + 1}.symm ξ)))
    rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_symm_map,
      hnat T.unop T'.unop g.unop (uliftYonedaEquiv.{u + 1}.symm ξ)]
  · refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun ξ ↦ ?_))
    show q.hom.app T (uliftYonedaEquiv.{u + 1} (W T.unop (uliftYonedaEquiv.{u + 1}.symm ξ)))
      = z.hom.app T ξ
    rw [← uliftYonedaEquiv_comp, (hW T.unop (uliftYonedaEquiv.{u + 1}.symm ξ)).1,
      uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  · refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun ζ ↦ ?_))
    show uliftYonedaEquiv.{u + 1}
        (W T.unop (uliftYonedaEquiv.{u + 1}.symm (ι.hom.app T ζ)))
      = h.hom.app T ζ
    have hsplit : (𝟙 ((uliftYoneda.{u + 1}).obj T.unop)) ≫
        uliftYonedaEquiv.{u + 1}.symm (ι.hom.app T ζ)
        = uliftYonedaEquiv.{u + 1}.symm ζ ≫ ι.hom :=
      (Category.id_comp _).trans (uliftYonedaEquiv_symm_comp _ _).symm
    have key : W T.unop (uliftYonedaEquiv.{u + 1}.symm (ι.hom.app T ζ))
        = uliftYonedaEquiv.{u + 1}.symm ζ ≫ h.hom := by
      rw [← Category.id_comp (W T.unop (uliftYonedaEquiv.{u + 1}.symm (ι.hom.app T ζ)))]
      exact comp_lift_eq_of_comp_eq_of_isRepresentableThickening hι z hW _ _ _ hsplit.symm
    rw [key, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]
  · rintro f ⟨hf₁, hf₂⟩
    refine Sheaf.hom_ext (NatTrans.ext (funext fun T ↦ ConcreteCategory.hom_ext _ _ fun ξ ↦ ?_))
    show f.hom.app T ξ
      = uliftYonedaEquiv.{u + 1} (W T.unop (uliftYonedaEquiv.{u + 1}.symm ξ))
    have hfq : f.hom ≫ q.hom = z.hom := congrArg (fun k : Z ⟶ Y ↦ k.hom) hf₁
    have hιf : ι.hom ≫ f.hom = h.hom := congrArg (fun k : Z₀ ⟶ A ↦ k.hom) hf₂
    have hval : uliftYonedaEquiv.{u + 1}.symm ξ ≫ f.hom
        = W T.unop (uliftYonedaEquiv.{u + 1}.symm ξ) := by
      refine hWu T.unop _ _ ⟨?_, ?_⟩
      · rw [Category.assoc, hfq]
      · rw [← Category.assoc, ← (hι.rep.isPullback (uliftYonedaEquiv.{u + 1}.symm ξ)).w,
          Category.assoc, hιf]
    rw [← hval, uliftYonedaEquiv_comp, Equiv.apply_symm_apply]

/-- The reduction of an object of the category of Stacks 0DEG: the one Stacks 0AIN constructs
for the formal algebraic space `U`, `AlgebraicGeometry.FormalSpace.reduction`. Any two
reductions are canonically isomorphic by `AlgebraicGeometry.FormalSpace.Reduction.iso`, so
nothing depends on the choice, and
`AlgebraicGeometry.FormalSpace.isPullback_inclusion_liftSheafMap_map` identifies this one with
the fibre product `U ×_X X_red` that the source names. -/
noncomputable def objReduction' {X : FppfSheaf B S hS}
    (U : RepresentableEtaleFormalSpacesOver X) : Reduction B S hS U.obj.left :=
  reduction B S hS U.obj.left U.property.1

/-- The comparison functor is injective on morphisms. -/
theorem injective_spacesEtaleComparison_map {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (U U' : RepresentableEtaleFormalSpacesOver X) :
    Function.Injective fun f : U ⟶ U' ↦ (spacesEtaleComparison hX R).map f := by
  intro f₁ f₂ he
  have hl : (objReduction' U).map (objReduction' U') f₁.hom.left
      = (objReduction' U).map (objReduction' U') f₂.hom.left :=
    congrArg (fun k ↦ k.hom.left) he
  have hcross : (objReduction' U).inclusion ≫ f₂.hom.left
      = (objReduction' U).inclusion ≫ f₁.hom.left := by
    rw [← (objReduction' U).liftSheafMap_map (objReduction' U') f₁.hom.left,
      ← (objReduction' U).liftSheafMap_map (objReduction' U') f₂.hom.left, hl]
  have hh : ((objReduction' U).inclusion ≫ f₁.hom.left) ≫ U'.obj.hom
      = (objReduction' U).inclusion ≫ U.obj.hom := by
    rw [Category.assoc, Over.w f₁.hom]
  obtain ⟨g, -, hgu⟩ := existsUnique_hom_of_isRepresentableThickening
    (objReduction' U).isReduction.isRepresentableThickening U'.property.2 U.obj.hom hh
  exact ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    ((hgu f₁.hom.left ⟨Over.w f₁.hom, rfl⟩).trans
      (hgu f₂.hom.left ⟨Over.w f₂.hom, hcross⟩).symm))

/-- The comparison functor is surjective on morphisms. -/
theorem surjective_spacesEtaleComparison_map {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (U U' : RepresentableEtaleFormalSpacesOver X) :
    Function.Surjective fun f : U ⟶ U' ↦ (spacesEtaleComparison hX R).map f := by
  intro m
  have hw : m.hom.left ≫ (objReduction' U').map R U'.obj.hom
      = (objReduction' U).map R U.obj.hom := Over.w m.hom
  have e₁ : (objReduction' U').inclusion ≫ U'.obj.hom
      = liftSheafMap B S hS ((objReduction' U').map R U'.obj.hom) ≫ R.inclusion :=
    ((objReduction' U').liftSheafMap_map R U'.obj.hom).symm
  have e₂ : liftSheafMap B S hS m.hom.left ≫
        liftSheafMap B S hS ((objReduction' U').map R U'.obj.hom)
      = liftSheafMap B S hS ((objReduction' U).map R U.obj.hom) :=
    (liftSheafMap_comp B S hS m.hom.left
      ((objReduction' U').map R U'.obj.hom)).symm.trans (congrArg (liftSheafMap B S hS) hw)
  have hh : (liftSheafMap B S hS m.hom.left ≫ (objReduction' U').inclusion) ≫ U'.obj.hom
      = (objReduction' U).inclusion ≫ U.obj.hom := by
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun k ↦ liftSheafMap B S hS m.hom.left ≫ k) e₁) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg (fun k ↦ k ≫ R.inclusion) e₂) ?_
    exact (objReduction' U).liftSheafMap_map R U.obj.hom
  obtain ⟨g, ⟨hg₁, hg₂⟩, -⟩ := existsUnique_hom_of_isRepresentableThickening
    (objReduction' U).isReduction.isRepresentableThickening U'.property.2 U.obj.hom hh
  exact ⟨ObjectProperty.homMk (Over.homMk g hg₁), ObjectProperty.hom_ext _ (Over.OverMorphism.ext
    ((objReduction' U).eq_map (objReduction' U') g m.hom.left hg₂.symm).symm)⟩

/-- The comparison functor is bijective on morphisms: for `φ : U ⟶ X` and
`φ' : U' ⟶ X` representable by algebraic spaces and étale, with `U` and `U'` formal algebraic
spaces, the morphisms `U ⟶ U'` over `X` correspond bijectively to the morphisms
`U_red ⟶ U'_red` over `X_red`.

This is the source's "we omit the verification that the constructions are mutually inverse to
each other", on the side that needs the lifting of a morphism along the thickening
`U_red ⟶ U`: a morphism of reductions over `X_red` is, by the fibre-product description
`U'_red = U' ×_X X_red` of
`AlgebraicGeometry.FormalSpace.isPullback_inclusion_liftSheafMap_map`, the same thing as a
morphism `U_red ⟶ U'` over `X`, and such a morphism extends uniquely to `U ⟶ U'` over `X` by
`AlgebraicGeometry.FormalSpace.existsUnique_hom_of_isRepresentableThickening`. In both
directions the morphism of reductions is recovered from the extension by the characterisation
`AlgebraicGeometry.FormalSpace.Reduction.eq_map`, so no naturality has to be checked. -/
@[stacks 0DEG "bijectivity on morphisms: the source's 'we omit the verification that the
  constructions are mutually inverse to each other'"]
theorem bijective_spacesEtaleComparison_map {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (U U' : RepresentableEtaleFormalSpacesOver X) :
    Function.Bijective fun f : U ⟶ U' ↦ (spacesEtaleComparison hX R).map f :=
  ⟨injective_spacesEtaleComparison_map hX R U U', surjective_spacesEtaleComparison_map hX R U U'⟩

/-- The comparison functor is faithful. -/
@[stacks 0DEG "faithfulness of the comparison functor"]
theorem faithful_spacesEtaleComparison {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (spacesEtaleComparison hX R).Faithful :=
  ⟨fun {U U'} ↦ (bijective_spacesEtaleComparison_map hX R U U').1⟩

/-- The comparison functor is full. -/
@[stacks 0DEG "fullness of the comparison functor"]
theorem full_spacesEtaleComparison {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) :
    (spacesEtaleComparison hX R).Full :=
  ⟨fun {U U'} ↦ (bijective_spacesEtaleComparison_map hX R U U').2⟩

end AlgebraicGeometry.FormalSpace

end
