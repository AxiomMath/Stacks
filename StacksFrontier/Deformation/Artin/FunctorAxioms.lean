module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingObjectsFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableFromDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSite
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaRepresentableSources
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafRepresentability
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FunctorForm

/-!
# Artin's axioms for a functor, read on its category fibred in sets (Section 07XZ)

Section 07XZ translates the axioms of Section 07XJ for a category fibred in groupoids into
statements about a functor `F : (Sch/S)_{fppf}^{opp} ⟶ Sets`, through the category `𝒮_F` fibred in
sets attached to `F` (`AlgebraicGeometry.Stack.fibredCategory`, Stacks 0458). This file proves the
translations that the proof of Stacks 07Y1 needs in the direction from `F` to `𝒮_F`.

## Main results

* `Deformation.Artin.satisfiesRS_fibredCategory_of_satisfiesRSFunctor`: condition (RS) for `F`
  in the functor form gives condition (RS) of Stacks 07WP for `𝒮_F`. The converse is
  `Deformation.Artin.satisfiesRSFunctor_of_satisfiesRS`.

## References

* [Stacks Project, Tag 07XZ](https://stacks.math.columbia.edu/tag/07XZ)
* [Stacks Project, Tag 07WP](https://stacks.math.columbia.edu/tag/07WP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Deformation.Artin

open Functor

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Condition (RS) in the functor form gives condition (RS) of Stacks 07WP for `𝒮_F`.** The
fibres of `𝒮_F` are discrete, so the comparison functor of Stacks 07WP is, up to the
identification of the objects of a fibre with elements of `F`, the map
`F(Y') ⟶ F(Y) ×_{F(X)} F(X')`: its bijectivity gives essential surjectivity and fullness, and
faithfulness is automatic. -/
theorem satisfiesRS_fibredCategory_of_satisfiesRSFunctor (h : SatisfiesRSFunctor B S hS F) :
    SatisfiesRS B S hS (Stack.fibredCategory B S hS F).val.p
      (Stack.fibredCategory B S hS F).isFiberedInGroupoids := by
  intro X X' Y Y' i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  let : (Stack.fibredCategory B S hS F).val.p.IsFibered :=
    (Stack.fibredCategory B S hS F).isFiberedInGroupoids.isFibered
  let p := (Stack.fibredCategory B S hS F).val.p
  let c := p.chosenPullbacks
  let G := fiberSquareComparison p c j i j' i' w.symm
  have hRS := h i j i' j' w hX hX' hY hY' hX₁ hX'₁ hY₁ hY'₁ hci hpo
  have eq_of_pullback_hom : ∀ {V U : BigFppfOver B S hS} (g : V ⟶ U) {a b : F.obj (op U)},
      (((c.pullbackFunctor g).obj (fibredCategoryFiberMk a) : p.Fiber V) ⟶
        (c.pullbackFunctor g).obj (fibredCategoryFiberMk b)) → F.map g.op a = F.map g.op b := by
    intro V U g a b φ
    rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq] at φ
    exact eq_of_fiber_hom φ
  have hcomp : ∀ t : F.obj (op Y'), F.map j.op (F.map j'.op t) = F.map i.op (F.map i'.op t) := by
    intro t
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
      w]
  have : G.Faithful := ⟨fun {_ _} _ _ _ => Subsingleton.elim _ _⟩
  have : G.Full := by
    refine ⟨fun {z₁ z₂} φ => ?_⟩
    obtain ⟨t₁, rfl⟩ := exists_eq_fibredCategoryFiberMk z₁
    obtain ⟨t₂, rfl⟩ := exists_eq_fibredCategoryFiberMk z₂
    have h₁ : F.map j'.op t₁ = F.map j'.op t₂ := eq_of_pullback_hom j' φ.fst
    have h₂ : F.map i'.op t₁ = F.map i'.op t₂ := eq_of_pullback_hom i' φ.snd
    obtain ⟨t, -, ht⟩ := hRS (F.map j'.op t₁) (F.map i'.op t₁) (hcomp t₁)
    obtain rfl : t₁ = t₂ := (ht t₁ ⟨rfl, rfl⟩).trans (ht t₂ ⟨h₁.symm, h₂.symm⟩).symm
    refine ⟨𝟙 _, ?_⟩
    apply CategoricalPullback.hom_ext <;> exact Subsingleton.elim _ _
  have : G.EssSurj := by
    refine ⟨fun P => ?_⟩
    obtain ⟨x, y, e⟩ := P
    obtain ⟨a, rfl⟩ := exists_eq_fibredCategoryFiberMk x
    obtain ⟨b, rfl⟩ := exists_eq_fibredCategoryFiberMk y
    have hab : F.map j.op a = F.map i.op b := by
      have e' := e.hom
      rw [pullbackFunctor_obj_eq, pullbackFunctor_obj_eq] at e'
      exact eq_of_fiber_hom e'
    obtain ⟨t, ⟨ht₁, ht₂⟩, -⟩ := hRS a b hab
    refine ⟨fibredCategoryFiberMk t, ⟨CategoricalPullback.mkIso
      (eqToIso (by
        change (c.pullbackFunctor j').obj _ = _
        rw [pullbackFunctor_obj_eq, ht₁]))
      (eqToIso (by
        change (c.pullbackFunctor i').obj _ = _
        rw [pullbackFunctor_obj_eq, ht₂]))
      (Subsingleton.elim _ _)⟩⟩
  exact { }

/-- A morphism conjugated by the comparison isomorphisms of two self-equalities is itself. -/
theorem eq_of_eq_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {X Y : C} (g f : X ⟶ Y)
    (e₁ : X = X) (e₂ : Y = Y) (h : g = eqToHom e₁ ≫ f ≫ eqToHom e₂) : g = f := by
  simpa using h

/-- The element named by an object of a fibre of `𝒮_F` given by an element is that element. -/
theorem presheafFiberElement_fiberMk {V : BigFppfOver B S hS} (t : F.obj (op V)) :
    Stack.presheafFiberElement B S hS F (fibredCategoryFiberMk t) = t := rfl

/-- A morphism of `𝒮_F` between objects given by elements, lying over `f`, lies over `f` as a
morphism of the site: its base is `f`. -/
theorem base_eq_of_isHomLift {V U : BigFppfOver B S hS} {t : F.obj (op V)} {t' : F.obj (op U)}
    (f : V ⟶ U) (φ : (fibredCategoryFiberMk t).1 ⟶ (fibredCategoryFiberMk t').1)
    (hφ : (Stack.fibredCategory B S hS F).val.p.IsHomLift f φ) : φ.base = f := by
  have h := IsHomLift.fac' (Stack.fibredCategory B S hS F).val.p f φ
  exact eq_of_eq_eqToHom_comp_comp_eqToHom _ _ _ _ h

/-- A morphism of `𝒮_F` between objects given by elements, lying over `f`, shows that the element
of the source is the pullback along `f` of the element of the target. -/
private theorem eq_map_of_isHomLift {V U : BigFppfOver B S hS} {t : F.obj (op V)}
    {t' : F.obj (op U)} (f : V ⟶ U) (φ : (fibredCategoryFiberMk t).1 ⟶ (fibredCategoryFiberMk t').1)
    (hφ : (Stack.fibredCategory B S hS F).val.p.IsHomLift f φ) : t = F.map f.op t' := by
  have h := fiber_as_eq_of_hom φ
  rwa [base_eq_of_isHomLift f φ hφ] at h

/-- Descent of objects for `𝒮_F` along a cone whose image under `F` is a colimit: every element of
`F` at the cone point comes from a stage. -/
private theorem descentObj_fibredCategory_of_isColimit {I : Type u} [Category.{u} I]
    {D : I ⥤ BigFppfOver B S hS} {c : Cone D} (hcol : IsColimit (F.mapCocone c.op)) :
    DescentObj (Stack.fibredCategory B S hS F).val.p D c := by
  intro x
  obtain ⟨t, rfl⟩ := exists_eq_fibredCategoryFiberMk x
  obtain ⟨⟨i⟩, a, ha⟩ := Types.jointly_surjective_of_isColimit hcol t
  obtain ⟨δ, hδ⟩ := Stack.presheafFiberHom B S hS F (c.π.app i) (fibredCategoryFiberMk t)
    (fibredCategoryFiberMk a) ha
  exact ⟨i, fibredCategoryFiberMk a, δ, hδ⟩

/-- Descent of morphisms for `𝒮_F` along a cofiltered cone whose image under `F` is a colimit:
two elements at a stage with the same image at the cone point agree at a later stage. -/
private theorem descentHom_fibredCategory_of_isColimit {I : Type u} [Category.{u} I]
    [IsCofiltered I] {D : I ⥤ BigFppfOver B S hS} {c : Cone D}
    (hcol : IsColimit (F.mapCocone c.op)) :
    DescentHom (Stack.fibredCategory B S hS F).val.p D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  obtain ⟨a, rfl⟩ := exists_eq_fibredCategoryFiberMk xi
  obtain ⟨b, rfl⟩ := exists_eq_fibredCategoryFiberMk yi
  obtain ⟨t, rfl⟩ := exists_eq_fibredCategoryFiberMk x
  obtain ⟨t', rfl⟩ := exists_eq_fibredCategoryFiberMk y
  have ht : t = F.map (c.π.app i).op a := eq_map_of_isHomLift _ δ hδ
  have ht' : t' = F.map (c.π.app i).op b := eq_map_of_isHomLift _ ε hε
  have htt : t = t' := by simpa using eq_map_of_isHomLift _ φ hφ
  have hab : (F.mapCocone c.op).ι.app (op i) a = (F.mapCocone c.op).ι.app (op i) b := by
    change F.map (c.π.app i).op a = F.map (c.π.app i).op b
    rw [← ht, ← ht', htt]
  obtain ⟨⟨k⟩, s, hs⟩ := (Types.FilteredColimit.isColimit_eq_iff' hcol a b).mp hab
  let s' : k ⟶ i := s.unop
  have hs' : F.map (D.map s').op a = F.map (D.map s').op b := hs
  let a' := F.map (D.map s').op a
  have hka : F.map (c.π.app k).op a' = t := by
    rw [ht, ← Functor.map_comp_apply, ← op_comp, c.w s']
  obtain ⟨dx, hdx⟩ := Stack.presheafFiberHom B S hS F (D.map s')
    (fibredCategoryFiberMk a') (fibredCategoryFiberMk a) rfl
  obtain ⟨dy, hdy⟩ := Stack.presheafFiberHom B S hS F (D.map s')
    (fibredCategoryFiberMk a') (fibredCategoryFiberMk b) hs'.symm
  obtain ⟨δk, hδk⟩ := Stack.presheafFiberHom B S hS F (c.π.app k)
    (fibredCategoryFiberMk t) (fibredCategoryFiberMk a') hka
  obtain ⟨ψ, hψ⟩ := Stack.presheafFiberHom B S hS F (𝟙 (D.obj k))
    (fibredCategoryFiberMk a') (fibredCategoryFiberMk a') (by simp)
  refine ⟨k, s', fibredCategoryFiberMk a', fibredCategoryFiberMk a', dx, dy, δk, ψ,
    hdx, hdy, hδk, hψ, ?_, ?_⟩
  · apply fibredCategory_hom_ext
    change δk.base ≫ dx.base = δ.base
    rw [base_eq_of_isHomLift _ δk hδk, base_eq_of_isHomLift _ dx hdx,
      base_eq_of_isHomLift _ δ hδ]
    exact c.w s'
  · apply fibredCategory_hom_ext
    change δk.base ≫ ψ.base ≫ dy.base = φ.base ≫ ε.base
    rw [base_eq_of_isHomLift _ δk hδk, base_eq_of_isHomLift _ dy hdy,
      base_eq_of_isHomLift _ ψ hψ, base_eq_of_isHomLift _ φ hφ, base_eq_of_isHomLift _ ε hε]
    have key : c.π.app k ≫ 𝟙 (D.obj k) ≫ D.map s' = 𝟙 c.pt ≫ c.π.app i := by
      rw [Category.id_comp, Category.id_comp]
      exact c.w s'
    exact key

/-- Descent of equalities of morphisms holds for `𝒮_F` along any cone of the site. -/
private theorem descentEq_fibredCategory {I : Type*} [Category I] (D : I ⥤ BigFppfOver B S hS)
    (c : Cone D) : DescentEq (Stack.fibredCategory B S hS F).val.p D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' _
  obtain ⟨a, rfl⟩ := exists_eq_fibredCategoryFiberMk xi
  obtain ⟨b, rfl⟩ := exists_eq_fibredCategoryFiberMk yi
  have hψψ : ψ = ψ' := fibredCategory_hom_ext _ _
    ((base_eq_of_isHomLift _ ψ hψ).trans (base_eq_of_isHomLift _ ψ' hψ').symm)
  obtain ⟨dx, hdx⟩ := Stack.presheafFiberHom B S hS F (D.map (𝟙 i))
    (fibredCategoryFiberMk a) (fibredCategoryFiberMk a) (by simp)
  exact ⟨i, 𝟙 i, fibredCategoryFiberMk a, dx, hdx, by rw [hψψ]⟩

/-- **Axiom [1] for `F` gives axiom [1] for `𝒮_F` (Section 07XZ).** If `F` is limit preserving in
the sense of Stacks 049J (along cofiltered inverse systems indexed in the universe of the site),
then `𝒮_F` is limit preserving in the sense of Stacks 07XL: the fibres of `𝒮_F` are the discrete
categories on the values of `F`, so the descent conditions of the colimit comparison are the
surjectivity and the injectivity of `colim F(Tᵢ) ⟶ F(T)`, and descent of equalities of morphisms
is automatic. -/
theorem isLimitPreserving_fibredCategory_of_limitPreserving
    (hF : LimitPreserving.{u, u, u, u, u + 1} (BigFppfOver.toScheme B S hS) F) :
    IsLimitPreserving.{u, u, u, u + 1, u} B S hS (Stack.fibredCategory B S hS F) := by
  intro I _ _ D c hc
  let p := (Stack.fibredCategory B S hS F).val.p
  have hp : p.IsFiberedInGroupoids := (Stack.fibredCategory B S hS F).isFiberedInGroupoids
  let : p.IsFibered := hp.isFibered
  let D' := D ⋙ BigAffineFppf.inclusion B S hS
  let c' := (BigAffineFppf.inclusion B S hS).mapCone c
  obtain ⟨hcol⟩ := hF I D' c' hc (fun i => (D.obj i).property) c.pt.property
  have := essSurj_of_descentObj p hp D' c' (descentObj_fibredCategory_of_isColimit hcol)
  have := full_of_descentHom p hp D' c' (descentHom_fibredCategory_of_isColimit hcol)
  have := faithful_of_descentEq p hp D' c' (descentEq_fibredCategory D' c')
  exact { }

/-- The 1-morphism `(Sch/V)_{fppf} ⟶ 𝒮_{h_V}` reading the slice of the site over `V` as the
category of elements of the presheaf represented by `V`; its underlying functor is an equivalence
(`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`). -/
def schemeToElements (V : BigFppfOver B S hS) :
    Stack.schemeFibredCategory B S hS V ⟶ Stack.fibredCategory B S hS (yoneda.obj V) :=
  (CatFiberedInGroupoids.homEquivBasedFunctor _ _).symm
    ⟨(PresheafOfCategories.sliceElementsEquivalenceOver V).hom.functor,
      (PresheafOfCategories.sliceElementsEquivalenceOver V).hom.w⟩

/-- The underlying functor of `Deformation.Artin.schemeToElements` is an equivalence. -/
theorem isEquivalence_schemeToElements (V : BigFppfOver B S hS) :
    Functor.IsEquivalence (schemeToElements (B := B) (S := S) (hS := hS) V).hom.toFunctor :=
  (PresheafOfCategories.sliceElementsEquivalenceOver V).toEquivalence.isEquivalence_functor

/-- **The 2-Yoneda 1-morphism of an element of `F` is the 1-morphism attached to the
corresponding map `h_V ⟶ F`.** For `t ∈ F(V)`, the 1-morphism `t : (Sch/V)_{fppf} ⟶ 𝒮_F`
built from chosen lifts sends `f : T ⟶ V` to the pair `(T, F(f)(t))`, which is where the slice
over `V`, read as the category of elements of `h_V`, is sent by the 1-morphism attached to
`yonedaEquiv.symm t : h_V ⟶ F` (Stacks 0458); a 1-morphism into `𝒮_F` is determined by its action
on objects. -/
theorem objectMorphism_fibredCategoryFiberMk {V : BigFppfOver B S hS} (t : F.obj (op V)) :
    Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F) (fibredCategoryFiberMk t) =
      schemeToElements V ≫ (Stack.associatedMap B S hS (yonedaEquiv.symm t)).1 := by
  apply Stack.hom_ext_of_obj
  intro x
  let p := (Stack.fibredCategory B S hS F).val.p
  let L := Functor.TwoYoneda.chosenLift p (Stack.fibredCategory B S hS F).isFiberedInGroupoids
    V (fibredCategoryFiberMk t) x
  have hlift : p.IsHomLift x.hom L.φ := L.isStronglyCartesian.toIsHomLift
  have hL : p.obj L.y = x.left := IsHomLift.domain_eq p x.hom L.φ
  exact (congrArg Subtype.val (fiberMk_eq_of_isHomLift x.hom t hL L.φ hlift)).trans
    (Stack.associatedMap_obj B S hS (yonedaEquiv.symm t)
      (⟨x.left, Discrete.mk x.hom⟩ : (Stack.fibredCategory B S hS (yoneda.obj V)).val.obj)).symm

/-- **Axiom (1) of Stacks 07Y1 for `𝒮_F`.** If the diagonal of `F` is representable by algebraic
spaces, then so is every 1-morphism `(Sch/V)_{fppf} ⟶ 𝒮_F` named by an element of `F`: it is the
1-morphism attached to the map `h_V ⟶ F`, which is representable by Stacks 0458, precomposed with
an equivalence. -/
theorem isRepresentableByAlgebraicSpaces_objectMorphism_of_diagonal
    (hdiag : Space.IsRepresentableByAlgebraicSpaces B S hS (diag F))
    {V : BigFppfOver B S hS} (y : (Stack.fibredCategory B S hS F).val.p.Fiber V) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS
      (Stack.objectMorphism B S hS (Stack.fibredCategory B S hS F) y).hom := by
  obtain ⟨t, rfl⟩ := exists_eq_fibredCategoryFiberMk y
  rw [objectMorphism_fibredCategoryFiberMk]
  have ha := Space.isRepresentableByAlgebraicSpaces_of_diagonal B S hS hdiag
    (isAlgebraicSpace_yoneda B S hS V) (yonedaEquiv.symm t)
  have hf := (Stack.isRepresentableByAlgebraicSpaces_iff_associatedMap B S hS _).mp ha
  exact (Stack.isRepresentableByAlgebraicSpaces_comp_iff B S hS
    (Stack.schemeFibredCategory B S hS V) (Stack.fibredCategory B S hS (yoneda.obj V))
    (Stack.fibredCategory B S hS F) (Stack.associatedMap B S hS (yonedaEquiv.symm t)).1.hom
    (schemeToElements V).hom (isEquivalence_schemeToElements V)).mp hf

end Deformation.Artin

end
