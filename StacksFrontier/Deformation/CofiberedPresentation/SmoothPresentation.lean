module

public import StacksFrontier.Deformation.CofiberedPresentation.VersalPresentation
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.RimSchlessingerCategory.ElementsCofibered
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare

/-!
# The groupoid in functors of a smooth morphism from a prorepresentable functor

Let `ℱ` be a predeformation category over `𝒞_Λ` and let `f : A|_{𝒞_Λ} ⟶ ℱ` be a smooth morphism
from the functor prorepresented by a Noetherian complete local `Λ`-algebra `A` (read as a
morphism of categories over `𝒞_Λ` out of its category of elements). The groupoid in functors
`(A|_{𝒞_Λ}, A|_{𝒞_Λ} ×_{f, ℱ, f} A|_{𝒞_Λ}, s, t, c)` attached to `f` is smooth and presents
`ℱ`. This generalizes `Deformation.presentationOfIsVersal` to a morphism which need not be the
one associated to a formal object.

The file also records that an equivalence over the base between the categories of elements of
two set-valued functors is an isomorphism of the functors, and that a morphism of categories
over `𝒞_Λ` followed by a smooth one is smooth when the first is an equivalence over the base.

## Main definitions

* `Deformation.smoothChartGroupoid`: the groupoid in functors attached to a morphism out of a
  prorepresentable functor.
* `Deformation.isoOfElementsEquivalenceOver`: an equivalence over the base between categories of
  elements, as an isomorphism of the functors.
* `Deformation.presentationOfIsSmooth`: the groupoid in functors of a smooth morphism out of a
  prorepresentable functor presents the target.

## Main results

* `Deformation.isSmooth_smoothChartGroupoid`: the groupoid in functors of a smooth morphism out
  of a prorepresentable functor is smooth.
* `Deformation.isSmooth_comp_of_equivalenceOver`: an equivalence over the base followed by a
  smooth morphism is smooth.
* `Deformation.exists_presentation_of_smoothChart`: a predeformation category with a smooth chart
  is presented by a smooth groupoid in functors with prorepresentable objects and arrows.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

universe u w uF v v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

namespace Deformation

section Elements

variable {C : Type u₁} [Category.{v₁} C]

/-- A morphism of elements over a morphism of the base, read through the transport of both
elements to the given base objects. -/
theorem elements_map_transport {R : C ⥤ Type v} {a b : R.Elements} (m : a ⟶ b) {T T' : C}
    (h₁ : a.1 = T) (h₂ : b.1 = T') (g : T ⟶ T')
    (hm : m.1 = eqToHom h₁ ≫ g ≫ eqToHom h₂.symm) :
    R.map g (R.map (eqToHom h₁) a.2) = R.map (eqToHom h₂) b.2 := by
  obtain @⟨A, x⟩ := a
  obtain @⟨B, y⟩ := b
  dsimp only at h₁ h₂
  subst h₁ h₂
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hm
  simp only [eqToHom_refl, Functor.map_id_apply]
  rw [← hm]
  exact m.2

/-- **An equivalence over the base between categories of elements is an isomorphism of the
functors.** The component at `T` sends `x ∈ P(T)` to the element of `Q` underlying the image of
`(T, x)`, transported back along the equality of its base with `T`. -/
noncomputable def isoOfElementsEquivalenceOver {P Q : C ⥤ Type v}
    (e : StacksRepresentableCFG.EquivalenceOver (Functor.Elements.π P)
      (Functor.Elements.π Q)) : P ≅ Q := by
  have hf : ∀ (T : C) (x : P.obj T), (e.hom.functor.obj (P.elementsMk T x)).1 = T :=
    fun T x => Functor.congr_obj e.hom.w (P.elementsMk T x)
  have hg : ∀ (T : C) (y : Q.obj T), (e.inv.functor.obj (Q.elementsMk T y)).1 = T :=
    fun T y => Functor.congr_obj e.inv.w (Q.elementsMk T y)
  let φ : ∀ T : C, P.obj T → Q.obj T := fun T x =>
    Q.map (eqToHom (hf T x)) (e.hom.functor.obj (P.elementsMk T x)).2
  let ψ : ∀ T : C, Q.obj T → P.obj T := fun T y =>
    P.map (eqToHom (hg T y)) (e.inv.functor.obj (Q.elementsMk T y)).2
  have hφnat : ∀ {T T' : C} (g : T ⟶ T') (x : P.obj T),
      Q.map g (φ T x) = φ T' (P.map g x) := by
    intro T T' g x
    let m : P.elementsMk T x ⟶ P.elementsMk T' (P.map g x) := ⟨g, rfl⟩
    exact elements_map_transport (e.hom.functor.map m) (hf T x) (hf T' (P.map g x)) g
      (Functor.congr_hom e.hom.w m)
  have hψφ : ∀ (T : C) (x : P.obj T), ψ T (φ T x) = x := by
    intro T x
    let n : e.hom.functor.obj (P.elementsMk T x) ⟶ Q.elementsMk T (φ T x) :=
      ⟨eqToHom (hf T x), rfl⟩
    let c := e.unitIso.hom.app (P.elementsMk T x) ≫ e.inv.functor.map n
    have := e.isHomLift_unitIso_hom_app (P.elementsMk T x)
    have hu := IsHomLift.fac' (Functor.Elements.π P)
      (𝟙 ((Functor.Elements.π P).obj (P.elementsMk T x))) (e.unitIso.hom.app (P.elementsMk T x))
    have hn := Functor.congr_hom e.inv.w n
    have hc : c.1 = eqToHom (rfl : (P.elementsMk T x).1 = T) ≫ 𝟙 T ≫
        eqToHom (hg T (φ T x)).symm := by
      change (e.unitIso.hom.app (P.elementsMk T x)).1 ≫ (e.inv.functor.map n).1 = _
      change (e.unitIso.hom.app (P.elementsMk T x)).1 = _ at hu
      change (e.inv.functor.map n).1 = _ at hn
      rw [hu, hn]
      change _ ≫ (eqToHom _ ≫ eqToHom (hf T x) ≫ eqToHom _) = _
      simp
    simpa using (elements_map_transport c rfl (hg T (φ T x)) (𝟙 T) hc).symm
  have hφψ : ∀ (T : C) (y : Q.obj T), φ T (ψ T y) = y := by
    intro T y
    let n : e.inv.functor.obj (Q.elementsMk T y) ⟶ P.elementsMk T (ψ T y) :=
      ⟨eqToHom (hg T y), rfl⟩
    let c := e.counitIso.inv.app (Q.elementsMk T y) ≫ e.hom.functor.map n
    have := e.isHomLift_counitIso_inv_app (Q.elementsMk T y)
    have hu := IsHomLift.fac' (Functor.Elements.π Q)
      (𝟙 ((Functor.Elements.π Q).obj (Q.elementsMk T y))) (e.counitIso.inv.app (Q.elementsMk T y))
    have hn := Functor.congr_hom e.hom.w n
    have hc : c.1 = eqToHom (rfl : (Q.elementsMk T y).1 = T) ≫ 𝟙 T ≫
        eqToHom (hf T (ψ T y)).symm := by
      change (e.counitIso.inv.app (Q.elementsMk T y)).1 ≫ (e.hom.functor.map n).1 = _
      change (e.counitIso.inv.app (Q.elementsMk T y)).1 = _ at hu
      change (e.hom.functor.map n).1 = _ at hn
      rw [hu, hn]
      change _ ≫ (eqToHom _ ≫ eqToHom (hg T y) ≫ eqToHom _) = _
      simp
    simpa using (elements_map_transport c rfl (hf T (ψ T y)) (𝟙 T) hc).symm
  exact NatIso.ofComponents
    (fun T => Equiv.toIso
      { toFun := φ T
        invFun := ψ T
        left_inv := hψφ T
        right_inv := hφψ T })
    (fun {T T'} g => by
      ext x
      exact (hφnat g x).symm)

end Elements

section EquivalenceOver

variable {C : Type u₁} [Category.{v₁} C]

/-- **A fully faithful essentially surjective functor over the base out of a category cofibered
in groupoids is an equivalence over the base.** -/
noncomputable def equivalenceOverOfCofibered {D₁ : Type u₂} [Category.{v₂} D₁]
    {D₂ : Type uF} [Category.{v} D₂] {p : D₁ ⥤ C} {q : D₂ ⥤ C}
    (hp : IsCofiberedInGroupoids p) (K : D₁ ⥤ D₂) (hw : K ⋙ q = p)
    [K.Full] [K.Faithful] [K.EssSurj] : StacksRepresentableCFG.EquivalenceOver p q := by
  let φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q) := ⟨K, hw⟩
  let : φ.toFunctor.EssSurj := inferInstanceAs K.EssSurj
  have hess : ∀ A : C, (Fiber.mapOfComp p q K hw A).EssSurj :=
    fun A => essSurj_fiberFunctor hp φ A
  let e := isEquivalenceOver_of_exists_vertical_iso hw
    (exists_vertical_iso_of_fiber_essSurj hw hess)
  refine ⟨⟨K, hw⟩, ⟨e.inv, e.inv_over⟩, e.unitIso.symm, e.counitIso, ?_, ?_⟩
  · ext X
    let : p.IsHomLift (𝟙 (p.obj ((K ⋙ e.inv).obj X))) (e.unitIso.hom.app X) := e.unit_vertical X
    let := IsHomLift.lift_id_inv_isIso p (p.obj ((K ⋙ e.inv).obj X)) (e.unitIso.hom.app X)
    simpa using IsHomLift.fac' p (𝟙 (p.obj ((K ⋙ e.inv).obj X))) (inv (e.unitIso.hom.app X))
  · ext X
    let : q.IsHomLift (𝟙 (q.obj ((e.inv ⋙ K).obj X))) (e.counitIso.hom.app X) :=
      e.counit_vertical X
    simpa using IsHomLift.fac' q (𝟙 (q.obj ((e.inv ⋙ K).obj X))) (e.counitIso.hom.app X)

end EquivalenceOver

section TwoFibreProduct

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₃} [Category.{v₃} 𝒳] {𝒳' : Type u₄}
  [Category.{v₄} 𝒳'] {𝒮 : Type u₅} [Category.{v₅} 𝒮] {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒳' : 𝒳' ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞}

/-- A morphism of the source of a functor over the base lies over a morphism exactly when its
image does. -/
theorem isHomLift_map_iff_of_over {F : 𝒳' ⥤ 𝒳} (hF : F ⋙ p𝒳 = p𝒳') {R S : 𝒞} (f : R ⟶ S)
    {a b : 𝒳'} (φ : a ⟶ b) : p𝒳.IsHomLift f (F.map φ) ↔ p𝒳'.IsHomLift f φ := by
  subst hF
  constructor
  · intro h
    have h1 := IsHomLift.domain_eq p𝒳 f (F.map φ)
    have h2 := IsHomLift.codomain_eq p𝒳 f (F.map φ)
    exact IsHomLift.of_fac' (F ⋙ p𝒳) f φ h1 h2 (IsHomLift.fac' p𝒳 f (F.map φ))
  · intro h
    have h1 := IsHomLift.domain_eq (F ⋙ p𝒳) f φ
    have h2 := IsHomLift.codomain_eq (F ⋙ p𝒳) f φ
    exact IsHomLift.of_fac' p𝒳 f (F.map φ) h1 h2 (IsHomLift.fac' (F ⋙ p𝒳) f φ)

/-- **The 2-fibre product is invariant under equivalences over the base of its legs.** For an
equivalence `e : 𝒳' ≃ 𝒳` over `𝒞` and a functor `F : 𝒳 ⥤ 𝒮` over `𝒞`, the 2-fibre product
`𝒳' ×_{F ∘ e, 𝒮, F ∘ e} 𝒳'` is equivalent over `𝒞` to `𝒳 ×_{F, 𝒮, F} 𝒳`. -/
noncomputable def twoFibreProductEquivalenceOver (e : StacksRepresentableCFG.EquivalenceOver p𝒳' p𝒳)
    (F : 𝒳 ⥤ 𝒮) (hF : F ⋙ p𝒮 = p𝒳) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor p𝒳' p𝒳' p𝒮 (e.hom.functor ⋙ F) (e.hom.functor ⋙ F))
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F F) := by
  haveI : e.hom.functor.IsEquivalence := e.isEquivalence_hom_functor
  let E := e.hom.functor
  have hE : E ⋙ p𝒳 = p𝒳' := e.hom.w
  let M : TwoFibreProductOver p𝒳' p𝒳' p𝒮 (E ⋙ F) (E ⋙ F) ⥤
      TwoFibreProductOver p𝒳 p𝒳 p𝒮 F F :=
    { obj := fun P =>
        { base := P.base
          x := E.obj P.x
          y := E.obj P.y
          hx := (Functor.congr_obj hE P.x).trans P.hx
          hy := (Functor.congr_obj hE P.y).trans P.hy
          iso := P.iso
          vertical := P.vertical }
      map := fun {P Q} f =>
        { hbase := f.hbase
          a := E.map f.a
          b := E.map f.b
          ha := (isHomLift_map_iff_of_over hE f.hbase f.a).2 f.ha
          hb := (isHomLift_map_iff_of_over hE f.hbase f.b).2 f.hb
          w := f.w }
      map_id := fun P => by
        apply TwoFibreProductOver.Hom.ext
        · rfl
        · exact E.map_id P.x
        · exact E.map_id P.y
      map_comp := fun f g => by
        apply TwoFibreProductOver.Hom.ext
        · rfl
        · exact E.map_comp f.a g.a
        · exact E.map_comp f.b g.b }
  have hM : M ⋙ TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F F =
      TwoFibreProductOver.structureFunctor p𝒳' p𝒳' p𝒮 (E ⋙ F) (E ⋙ F) := rfl
  haveI : M.Faithful := ⟨fun {P Q} f g h => by
    apply TwoFibreProductOver.Hom.ext'
    · exact E.map_injective (congrArg TwoFibreProductOver.Hom.a h)
    · exact E.map_injective (congrArg TwoFibreProductOver.Hom.b h)⟩
  haveI : M.Full := ⟨fun {P Q} f => by
    refine ⟨{ hbase := f.hbase
              a := E.preimage f.a
              b := E.preimage f.b
              ha := (isHomLift_map_iff_of_over hE f.hbase _).1 (by simpa using f.ha)
              hb := (isHomLift_map_iff_of_over hE f.hbase _).1 (by simpa using f.hb)
              w := by simpa using f.w }, ?_⟩
    apply TwoFibreProductOver.Hom.ext
    · rfl
    · exact E.map_preimage f.a
    · exact E.map_preimage f.b⟩
  have hvert : CategoryTheory.Functor.HasVerticalPreimages
      (TwoFibreProductOver.structureFunctor p𝒳' p𝒳' p𝒮 (E ⋙ F) (E ⋙ F))
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F F) M := by
    intro Q
    let c₁ := e.counitIso.app Q.x
    let c₂ := e.counitIso.app Q.y
    have hc₁ : p𝒳.IsHomLift (𝟙 (p𝒳.obj Q.x)) c₁.hom := e.isHomLift_counitIso_hom_app Q.x
    have hc₂ : p𝒳.IsHomLift (𝟙 (p𝒳.obj Q.y)) c₂.hom := e.isHomLift_counitIso_hom_app Q.y
    have hc₁' : p𝒳.IsHomLift (𝟙 (p𝒳.obj Q.x)) c₁.inv := e.isHomLift_counitIso_inv_app Q.x
    have hc₂' : p𝒳.IsHomLift (𝟙 (p𝒳.obj Q.y)) c₂.inv := e.isHomLift_counitIso_inv_app Q.y
    rw [Q.hx] at hc₁ hc₁'
    rw [Q.hy] at hc₂ hc₂'
    have hF₁ : p𝒮.IsHomLift (𝟙 Q.base) (F.map c₁.hom) :=
      (isHomLift_map_iff_of_over hF _ _).2 hc₁
    have hF₂ : p𝒮.IsHomLift (𝟙 Q.base) (F.map c₂.inv) :=
      (isHomLift_map_iff_of_over hF _ _).2 hc₂'
    have hiso : p𝒮.IsHomLift (𝟙 Q.base) (F.map c₁.hom ≫ Q.iso.hom ≫ F.map c₂.inv) := by
      have := Q.vertical
      have := hF₁
      have := hF₂
      simpa using (inferInstance : p𝒮.IsHomLift (𝟙 Q.base ≫ 𝟙 Q.base ≫ 𝟙 Q.base)
        (F.map c₁.hom ≫ Q.iso.hom ≫ F.map c₂.inv))
    let o : TwoFibreProductOver p𝒳' p𝒳' p𝒮 (E ⋙ F) (E ⋙ F) :=
      { base := Q.base
        x := e.inv.functor.obj Q.x
        y := e.inv.functor.obj Q.y
        hx := (Functor.congr_obj e.inv.w Q.x).trans Q.hx
        hy := (Functor.congr_obj e.inv.w Q.y).trans Q.hy
        iso := F.mapIso c₁ ≪≫ Q.iso ≪≫ F.mapIso c₂.symm
        vertical := hiso }
    let α : Q ⟶ M.obj o :=
      { hbase := 𝟙 Q.base
        a := c₁.inv
        b := c₂.inv
        ha := hc₁'
        hb := hc₂'
        w := by
          change F.map c₁.inv ≫ (F.map c₁.hom ≫ Q.iso.hom ≫ F.map c₂.inv) = Q.iso.hom ≫ F.map c₂.inv
          simp [← F.map_comp_assoc] }
    have : IsIso α := TwoFibreProductOver.isIso_of_isIso_components p𝒳 p𝒳 p𝒮 F F α
      inferInstance inferInstance
    exact ⟨o, rfl, asIso α, by
      change (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F F).IsHomLift (𝟙 Q.base) α
      exact (inferInstance : (TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F F).IsHomLift
        ((TwoFibreProductOver.structureFunctor p𝒳 p𝒳 p𝒮 F F).map α) α)⟩
  exact StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver hM
    (isEquivalenceOver_of_exists_vertical_iso hM hvert)

/-- **The 2-fibre product is invariant under a vertical isomorphism of a leg.** For functors
`F : 𝒳 ⥤ 𝒮` and `G, G' : 𝒳' ⥤ 𝒮` over `𝒞` and a natural isomorphism `G ≅ G'` with vertical
components, `𝒳 ×_{F, 𝒮, G} 𝒳'` is equivalent over `𝒞` to `𝒳 ×_{F, 𝒮, G'} 𝒳'`. -/
noncomputable def twoFibreProductEquivalenceOverOfIso (F : 𝒳 ⥤ 𝒮) {G G' : 𝒳' ⥤ 𝒮} (α : G ≅ G')
    (hα : ∀ y, p𝒮.IsHomLift (𝟙 (p𝒳'.obj y)) (α.hom.app y)) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G)
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G') := by
  have hvert : ∀ P : TwoFibreProductOver p𝒳 p𝒳' p𝒮 F G,
      p𝒮.IsHomLift (𝟙 P.base) (P.iso.hom ≫ α.hom.app P.y) := by
    intro P
    have h1 := hα P.y
    rw [P.hy] at h1
    have := P.vertical
    have := h1
    simpa using (inferInstance : p𝒮.IsHomLift (𝟙 P.base ≫ 𝟙 P.base) (P.iso.hom ≫ α.hom.app P.y))
  let M : TwoFibreProductOver p𝒳 p𝒳' p𝒮 F G ⥤ TwoFibreProductOver p𝒳 p𝒳' p𝒮 F G' :=
    { obj := fun P =>
        { base := P.base
          x := P.x
          y := P.y
          hx := P.hx
          hy := P.hy
          iso := P.iso ≪≫ α.app P.y
          vertical := hvert P }
      map := fun {P Q} f =>
        { hbase := f.hbase
          a := f.a
          b := f.b
          ha := f.ha
          hb := f.hb
          w := by
            change F.map f.a ≫ Q.iso.hom ≫ α.hom.app Q.y = (P.iso.hom ≫ α.hom.app P.y) ≫ G'.map f.b
            rw [← Category.assoc, f.w, Category.assoc, Category.assoc, α.hom.naturality] }
      map_id := fun P => rfl
      map_comp := fun f g => rfl }
  have hM : M ⋙ TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G' =
      TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G := rfl
  haveI : M.Faithful := ⟨fun {P Q} f g h => by
    apply TwoFibreProductOver.Hom.ext'
    · exact congrArg (fun m : M.obj P ⟶ M.obj Q => m.a) h
    · exact congrArg (fun m : M.obj P ⟶ M.obj Q => m.b) h⟩
  haveI : M.Full := ⟨fun {P Q} f => by
    refine ⟨{ hbase := f.hbase
              a := f.a
              b := f.b
              ha := f.ha
              hb := f.hb
              w := ?_ }, ?_⟩
    · have h := f.w
      change F.map f.a ≫ Q.iso.hom ≫ α.hom.app Q.y = (P.iso.hom ≫ α.hom.app P.y) ≫ G'.map f.b at h
      rw [Category.assoc, ← α.hom.naturality, ← Category.assoc, ← Category.assoc] at h
      exact (cancel_mono (α.hom.app Q.y)).mp h
    · rfl⟩
  have hv : CategoryTheory.Functor.HasVerticalPreimages
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G)
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G') M := by
    intro Q
    have h1 : p𝒮.IsHomLift (𝟙 Q.base) (α.inv.app Q.y) := by
      have h := hα Q.y
      rw [Q.hy] at h
      have := h
      have h2 := IsHomLift.lift_id_inv_isIso p𝒮 Q.base (α.hom.app Q.y)
      rwa [show CategoryTheory.inv (α.hom.app Q.y) = α.inv.app Q.y by simp] at h2
    let o : TwoFibreProductOver p𝒳 p𝒳' p𝒮 F G :=
      { base := Q.base
        x := Q.x
        y := Q.y
        hx := Q.hx
        hy := Q.hy
        iso := Q.iso ≪≫ (α.app Q.y).symm
        vertical := by
          have := Q.vertical
          have := h1
          simpa using (inferInstance :
            p𝒮.IsHomLift (𝟙 Q.base ≫ 𝟙 Q.base) (Q.iso.hom ≫ α.inv.app Q.y)) }
    let β : Q ⟶ M.obj o :=
      { hbase := 𝟙 Q.base
        a := 𝟙 Q.x
        b := 𝟙 Q.y
        ha := by rw [← Q.hx]; infer_instance
        hb := by rw [← Q.hy]; infer_instance
        w := by
          change F.map (𝟙 Q.x) ≫ (Q.iso.hom ≫ α.inv.app Q.y) ≫ α.hom.app Q.y =
            Q.iso.hom ≫ G'.map (𝟙 Q.y)
          simp }
    have : IsIso β := TwoFibreProductOver.isIso_of_isIso_components p𝒳 p𝒳' p𝒮 F G' β
      inferInstance inferInstance
    exact ⟨o, rfl, asIso β,
      (inferInstance : (TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G').IsHomLift
        ((TwoFibreProductOver.structureFunctor p𝒳 p𝒳' p𝒮 F G').map β) β)⟩
  exact StacksRepresentableCFG.EquivalenceOver.ofFunctorIsEquivalenceOver hM
    (isEquivalenceOver_of_exists_vertical_iso hM hv)

end TwoFibreProduct

section Smooth

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **A morphism of categories over `𝒞_Λ` preceded by an equivalence over `𝒞_Λ` out of a
category cofibered in groupoids is smooth when the morphism is.** -/
public theorem isSmooth_comp_of_equivalenceOver
    {𝓕 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓖 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    {𝓗 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, v, w} Λ k)}
    (e : StacksRepresentableCFG.EquivalenceOver 𝓕.p 𝓖.p) (_h𝓕 : IsCofiberedInGroupoids 𝓕.p)
    (m : BasedFunctor 𝓖 𝓗) (hm : IsSmooth m) :
    IsSmooth (BasedFunctor.comp ⟨e.hom.functor, e.hom.w⟩ m) := by
  refine isSmooth_comp _ m ?_ hm
  intro B A f _ y x g hg
  let := hg
  have : e.hom.functor.IsEquivalence := e.isEquivalence_hom_functor
  let x₁ := e.inv.functor.obj y
  have hx₁ : 𝓕.p.obj x₁ = 𝓖.p.obj y := Functor.congr_obj e.inv.w y
  have hy : 𝓖.p.obj y = B := IsHomLift.domain_eq 𝓖.p f g
  let c : e.hom.functor.obj x₁ ⟶ y := e.counitIso.hom.app y
  have hc : 𝓖.p.IsHomLift (𝟙 (𝓖.p.obj y)) c := e.isHomLift_counitIso_hom_app y
  have hcomp : 𝓖.p.IsHomLift f (c ≫ g) := by
    rw [hy] at hc
    let := hc
    exact IsHomLift.comp_lift_id_left 𝓖.p f g c
  let h := e.hom.functor.preimage (c ≫ g)
  have hh : e.hom.functor.map h = c ≫ g := e.hom.functor.map_preimage _
  refine ⟨x₁, h, c, ?_, hy ▸ hc, hh⟩
  have hl : 𝓖.p.IsHomLift f (e.hom.functor.map h) := hh ▸ hcomp
  have hw := e.hom.w
  have h1 := Functor.congr_hom hw h
  have hf1 := IsHomLift.fac' 𝓖.p f (e.hom.functor.map h)
  simp only [Functor.comp_map] at h1
  rw [hf1] at h1
  have hd : 𝓕.p.obj x₁ = B := hx₁.trans hy
  have hx : 𝓕.p.obj x = A :=
    (Functor.congr_obj hw x).symm.trans (IsHomLift.codomain_eq 𝓖.p f g)
  exact IsHomLift.of_fac' 𝓕.p f h hd hx (by
    have h2 := h1.symm
    simp only [eqToHom_comp_iff, comp_eqToHom_iff, Category.assoc] at h2
    rw [h2]
    simp)

end Smooth

section Presentation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k] {F : Type uF}
  [Category.{w} F]

/-- The groupoid in functors `(A|_{𝒞_Λ}, A|_{𝒞_Λ} ×_{f, ℱ, f} A|_{𝒞_Λ}, s, t, c)` attached to a
morphism `f : A|_{𝒞_Λ} ⟶ ℱ` out of a prorepresentable functor. -/
noncomputable abbrev smoothChartGroupoid (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : CompleteLocalAlgCat.{u, w, w} Λ k)
    (f : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda A)))
      (BasedCategory.ofFunctor p)) :
    GroupoidInFunctors.{_, w, w} (ArtinianLocalAlgCat.{u, w, w} Λ k) :=
  (presentationGroupoid p (restrictedCoyoneda A) f.toFunctor f.w hp).toGroupoidInFunctors

/-- The groupoid in functors of a smooth morphism out of a prorepresentable functor is
smooth. -/
public theorem isSmooth_smoothChartGroupoid (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : CompleteLocalAlgCat.{u, w, w} Λ k)
    (f : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda A)))
      (BasedCategory.ofFunctor p)) (hf : IsSmooth f) :
    GroupoidInFunctors.IsSmooth (smoothChartGroupoid p hp A f) :=
  isSmooth_presentationGroupoid p _ _ hp hf

/-- The objects of the groupoid of a morphism out of `A|_{𝒞_Λ}` are prorepresented by `A`. -/
public noncomputable def smoothChartGroupoidObjectsIso (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (A : CompleteLocalAlgCat.{u, w, w} Λ k)
    (f : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda A)))
      (BasedCategory.ofFunctor p)) :
    (smoothChartGroupoid p hp A f).objects ≅ restrictedCoyoneda A :=
  Functor.isoWhiskerLeft _ uliftFunctorTrivial ≪≫ Functor.rightUnitor _

/-- The groupoid in functors of a smooth morphism out of a prorepresentable functor into a
predeformation category presents the category. -/
public noncomputable def presentationOfIsSmooth (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (A : CompleteLocalAlgCat.{u, w, w} Λ k)
    (f : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda A)))
      (BasedCategory.ofFunctor p)) (hf : IsSmooth f) :
    Presentation (smoothChartGroupoid p hp.cofibered A f) p := by
  classical
  let U := restrictedCoyoneda.{u, w, w} A
  have hu₀ : Nonempty (U.obj (residueFieldObject.{u, w, w} Λ k)) :=
    ⟨(restrictedCoyoneda_isPredeformationFunctor.{u, w, w} A).some.default⟩
  let y₀ : U.Elements := U.elementsMk (residueFieldObject.{u, w, w} Λ k) hu₀.some
  have h₀ : (fiberFunctor f (residueFieldObject.{u, w, w} Λ k)).EssSurj :=
    ⟨fun z => ⟨⟨y₀, rfl⟩, by
      obtain ⟨E⟩ := hp.specialFiber
      exact ⟨E.unitIso.app _ ≪≫ E.inverse.mapIso (eqToIso (Discrete.ext (Subsingleton.elim _ _))) ≪≫
        (E.unitIso.app z).symm⟩⟩⟩
  have heq := presentationMorphism_isEquivalence_of_isSmooth_of_fiber_essSurj
    p U f hp.cofibered hf h₀
  let : (presentationMorphism p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp.cofibered)).1.Full :=
    presentationMorphism_full p U f.toFunctor f.w _ hp.cofibered
  let : (presentationMorphism p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp.cofibered)).1.Faithful :=
    presentationMorphism_faithful p U f.toFunctor f.w _
  let : (presentationMorphism p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp.cofibered)).1.EssSurj :=
    heq.essSurj
  exact presentationOfQuotientEquivalence _ p _
    (presentationMorphism p U f.toFunctor f.w
      (presentationGroupoid p U f.toFunctor f.w hp.cofibered)).2.1

/-- **The groupoid in functors of a smooth chart.** Let `ℱ` be a predeformation
category over `𝒞_Λ`, let `ℱ_V` be a category over `𝒞_Λ` equivalent over `𝒞_Λ` to the category
of elements of `A|_{𝒞_Λ}`, and let `g : ℱ_V ⥤ ℱ` be a smooth morphism of categories over `𝒞_Λ`
whose 2-fibre product `ℱ_V ×_{g, ℱ, g} ℱ_V` is equivalent over `𝒞_Λ` to the category of elements
of `B|_{𝒞_Λ}`. Then `ℱ` is presented by a smooth groupoid in functors whose functors of objects
and of arrows are prorepresented by `A` and by `B`. -/
public theorem exists_presentation_of_smoothChart (p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k)
    (hp : IsPredeformationCategory.{u, w, w} p) (A B : CompleteLocalAlgCat.{u, w, w} Λ k)
    {FV : Type u₂} [Category.{v₂} FV] {pV : FV ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}
    (eV : StacksRepresentableCFG.EquivalenceOver (Functor.Elements.π (restrictedCoyoneda A)) pV)
    (g : FV ⥤ F) (hg : g ⋙ p = pV)
    (hsm : IsSmooth
      (⟨g, hg⟩ : BasedFunctor (BasedCategory.ofFunctor pV) (BasedCategory.ofFunctor p)))
    (eB : StacksRepresentableCFG.EquivalenceOver (TwoFibreProductOver.structureFunctor pV pV p g g)
      (Functor.Elements.π (restrictedCoyoneda B))) :
    ∃ G : GroupoidInFunctors.{_, w, w} (ArtinianLocalAlgCat.{u, w, w} Λ k),
      GroupoidInFunctors.IsSmooth G ∧ Nonempty (Presentation G p) ∧
        Nonempty (G.objects ≅ restrictedCoyoneda A) ∧
          Nonempty (G.arrows ≅ restrictedCoyoneda B) := by
  let U := restrictedCoyoneda.{u, w, w} A
  let f₁ : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor pV) := ⟨eV.hom.functor, eV.hom.w⟩
  let f : BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π U))
      (BasedCategory.ofFunctor p) := BasedFunctor.comp f₁ ⟨g, hg⟩
  have hf : IsSmooth f :=
    isSmooth_comp_of_equivalenceOver (𝓕 := BasedCategory.ofFunctor (Functor.Elements.π U))
      (𝓖 := BasedCategory.ofFunctor pV) eV (isCofiberedInGroupoids_elementsProjection U)
      (⟨g, hg⟩ : BasedFunctor (BasedCategory.ofFunctor pV) (BasedCategory.ofFunctor p)) hsm
  let P := presentationGroupoid p U f.toFunctor f.w hp.cofibered
  refine ⟨smoothChartGroupoid p hp.cofibered A f,
    isSmooth_smoothChartGroupoid p hp.cofibered A f hf,
    ⟨presentationOfIsSmooth p hp A f hf⟩, ⟨smoothChartGroupoidObjectsIso p hp.cofibered A f⟩, ?_⟩
  let : Category (TwoFibreProductOver
      (Functor.Elements.π U) (Functor.Elements.π U) p f.toFunctor f.toFunctor) :=
    TwoFibreProductOver.instCategory
  have : P.fibreProductEquivalence.functor.IsEquivalence := inferInstance
  let E₁ : StacksRepresentableCFG.EquivalenceOver (Functor.Elements.π P.arrows)
      (TwoFibreProductOver.structureFunctor (Functor.Elements.π U) (Functor.Elements.π U) p
        f.toFunctor f.toFunctor) :=
    equivalenceOverOfCofibered (isCofiberedInGroupoids_elementsProjection P.arrows)
      P.fibreProductEquivalence.functor P.fibreProductOverBase
  let E₂ := twoFibreProductEquivalenceOver eV g hg
  exact ⟨isoOfElementsEquivalenceOver ((E₁.trans E₂).trans eB)⟩

end Presentation

end Deformation

end
