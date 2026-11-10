module

public import Mathlib.CategoryTheory.GuitartExact.KanExtension
public import Mathlib.CategoryTheory.GuitartExact.Opposite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct

/-!
# Base change for presheaves on categories fibred in groupoids (Stacks 075B)

Let `p𝒳 : 𝒳 ⥤ 𝒞`, `p𝒴' : 𝒴' ⥤ 𝒞` and `p𝒴 : 𝒴 ⥤ 𝒞` be categories fibred in groupoids and let
`f : 𝒳 ⥤ 𝒴`, `g : 𝒴' ⥤ 𝒴` be 1-morphisms over `𝒞`. For the canonical 2-cartesian square

```
𝒴' ×_𝒴 𝒳 --- snd ---> 𝒳
   |                   |
  fst                  f
   |                   |
   v                   v
  𝒴' ------ g ------>  𝒴
```

the canonical base-change transformation `g⁻¹ f_* ⟶ fst_* snd⁻¹` on presheaves is invertible.

The proof is the one in the Stacks Project, in the form Mathlib's Guitart-exactness API wants.
Direct image of presheaves is right Kan extension along the opposite functor and inverse image is
restriction, so the base-change transformation is `TwoSquare.op.ranBaseChange` of the square, and
it is invertible as soon as the opposite square is Guitart exact. By
`TwoSquare.guitartExact_iff_isConnected_rightwards` that reduces to connectedness of the category
of structured arrows rightwards at every `α : f.obj x ⟶ g.obj y'`, which is where the source's
equivalence of slice 2-fibre products lives: in a category fibred in groupoids `α` has a cartesian
lift, so the lift of `p𝒴.map α` through `p𝒴'` produces a *distinguished* object of that category,
and every object admits a morphism from it — hence the category is nonempty and zigzag-connected.

## Main results

* `CategoryTheory.TwoFibreProductOver.guitartExact_twoFibreProductSquare`: the canonical square of
  categories fibred in groupoids is Guitart exact.
* `CategoryTheory.TwoFibreProductOver.isIso_presheafRanBaseChange`: **Stacks 075B**.

## Implementation notes

The result is stated over an arbitrary base category `𝒞`, so in particular it applies to the big
fppf site over a scheme; the source states it over `(Sch/S)_fppf` only.

The Kan-extension existence hypotheses are instance arguments and carry no mathematics: they only
make the two direct-image functors available at the chosen coefficient universe, which is
independent of the site universes here.

Guitart exactness is proved for the square itself rather than for its opposite, because
`TwoSquare.GuitartExact` of a square gives it for the opposite square by
`Mathlib.CategoryTheory.GuitartExact.Opposite`, and the connectedness criterion is stated in the
unopposed direction.

## References

* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ t

variable {C : Type u₁} [Category.{v₁} C]
variable {X : Type u₂} [Category.{v₂} X]
variable {Y' : Type u₃} [Category.{v₃} Y']
variable {Y : Type u₄} [Category.{v₄} Y]

/-- The canonical 2-cartesian square of categories fibred in groupoids is Guitart exact.

Connectedness of the structured arrows rightwards at `α` is witnessed by one distinguished object,
built from a cartesian lift of `p𝒴.map α` along `p𝒴'`; every other object receives a morphism from
it, which is where the source's equivalence of slice 2-fibre products enters. -/
theorem guitartExact_twoFibreProductSquare
    (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C)
    (f : X ⥤ Y) (g : Y' ⥤ Y)
    (hX : pX.IsFiberedInGroupoids) (hY' : pY'.IsFiberedInGroupoids)
    (hY : pY.IsFiberedInGroupoids)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pY') :
    (TwoSquare.mk (TwoFibreProductOver.fst pX pY' pY f g)
      (TwoFibreProductOver.snd pX pY' pY f g) f g
      (TwoFibreProductOver.psiIso pX pY' pY f g).hom).GuitartExact := by
  cases hf
  cases hg
  let pX0 : X ⥤ C := f ⋙ pY
  let pY0 : Y' ⥤ C := g ⋙ pY
  let : Functor.IsFiberedInGroupoids pX0 := hX
  let : Functor.IsFiberedInGroupoids pY0 := hY'
  let : Functor.IsFiberedInGroupoids pY := hY
  let w := TwoSquare.mk (TwoFibreProductOver.fst pX0 pY0 pY f g)
    (TwoFibreProductOver.snd pX0 pY0 pY f g) f g
    (TwoFibreProductOver.psiIso pX0 pY0 pY f g).hom
  rw [TwoSquare.guitartExact_iff_isConnected_rightwards]
  intro x y' α
  let q := pY.map α
  obtain ⟨z, β, hβ⟩ := hY'.exists_lift q y' rfl
  let : pY.IsHomLift q (g.map β) := hY.isFibredOneMorphism rfl |>.map_isHomLift q β
  let : pY.IsStronglyCartesian q (g.map β) := hY.isStronglyCartesian_homLift q (g.map β)
  let : pY.IsStronglyCartesian q α := hY.isStronglyCartesian_homLift q α
  have hq : q = (Iso.refl (pY.obj (f.obj x))).hom ≫ q := by simp
  let e : f.obj x ≅ g.obj z :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := pY) (f := q) (f' := q) (g := Iso.refl (pY.obj (f.obj x)))
      hq (g.map β) α
  have he : pY.IsHomLift (𝟙 (pY.obj (f.obj x))) e.hom := by
    simpa [e] using
      (Functor.IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift pY hq (g.map β) α)
  let P₀ : TwoFibreProductOver pX0 pY0 pY f g :=
    ⟨pY.obj (f.obj x), x, z, rfl, IsHomLift.domain_eq pY0 q β, e, he⟩
  have hefac : e.hom ≫ g.map β = α := Functor.IsStronglyCartesian.fac pY q (g.map β) hq α
  let z₀ : w.StructuredArrowRightwards α :=
    TwoSquare.StructuredArrowRightwards.mk w α P₀ (𝟙 x) β (by
      change f.map (𝟙 x) ≫ e.hom ≫ g.map β = α
      rw [f.map_id, Category.id_comp, hefac])
  have hfrom (z₁ : w.StructuredArrowRightwards α) : z₀ ⟶ z₁ := by
    refine Classical.choice ?_
    obtain ⟨P, a, b, hab, rfl⟩ := TwoSquare.StructuredArrowRightwards.mk_surjective z₁
    change x ⟶ P.x at a
    change P.y ⟶ y' at b
    have hab' : f.map a ≫ P.iso.hom ≫ g.map b = α := hab
    let δ := pY.map (f.map a ≫ P.iso.hom)
    have hδ : q = δ ≫ pY0.map b := by
      calc
        q = pY.map α := rfl
        _ = pY.map (f.map a ≫ P.iso.hom) ≫ pY.map (g.map b) := by
          rw [← Functor.map_comp, Category.assoc, hab']
        _ = δ ≫ pY0.map b := rfl
    let : pY0.IsHomLift q β := hβ
    let : pY0.IsStronglyCartesian q β := hY'.isStronglyCartesian_homLift q β
    let : pY0.IsStronglyCartesian (pY0.map b) b :=
      hY'.isStronglyCartesian_homLift (pY0.map b) b
    let c := Functor.IsStronglyCartesian.map pY0 (pY0.map b) b hδ β
    let : pY0.IsHomLift δ c :=
      Functor.IsStronglyCartesian.map_isHomLift pY0 (pY0.map b) b hδ β
    have hcb : c ≫ b = β := Functor.IsStronglyCartesian.fac pY0 (pY0.map b) b hδ β
    have hcb' : pY0.map c = eqToHom P₀.hy ≫ δ := by
      simpa [P₀, pY0, Category.assoc] using IsHomLift.fac' pY0 δ c
    let : pY.IsHomLift (𝟙 P.base) P.iso.hom := P.vertical
    have hvP : pY.map P.iso.hom = eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hy.symm :=
      IsHomLift.fac' pY (𝟙 P.base) P.iso.hom
    have hcbase :
        eqToHom P₀.hy.symm ≫ pY0.map c ≫ eqToHom P.hy =
          eqToHom P₀.hx.symm ≫ pX0.map a ≫ eqToHom P.hx := by
      calc
        eqToHom P₀.hy.symm ≫ pY0.map c ≫ eqToHom P.hy = δ ≫ eqToHom P.hy := by
          rw [hcb']
          simp [Category.assoc]
        _ = eqToHom P₀.hx.symm ≫ pX0.map a ≫ eqToHom P.hx := by
          dsimp [δ, pX0]
          rw [Functor.map_comp, hvP]
          simp [P₀, Category.assoc]
    have hsquare : f.map a ≫ P.iso.hom = e.hom ≫ g.map c := by
      have hmapEq : pY.map (f.map a ≫ P.iso.hom) = pY.map (e.hom ≫ g.map c) := by
        let : pY.IsHomLift (𝟙 P₀.base) e.hom := he
        have hv₀ : pY.map e.hom = eqToHom P₀.hy.symm := by
          simpa [Category.id_comp] using IsHomLift.fac' pY (𝟙 P₀.base) e.hom
        have hc' : pY.map (g.map c) = pY0.map c := rfl
        simp [Functor.map_comp, hv₀, hc', hcb', hvP, δ, P₀]
      let : pY.IsHomLift (pY.map (e.hom ≫ g.map c)) (f.map a ≫ P.iso.hom) :=
        hmapEq ▸ inferInstance
      let : pY.IsHomLift (pY.map (e.hom ≫ g.map c)) (e.hom ≫ g.map c) := inferInstance
      have : pY.IsStronglyCartesian (pY.map (g.map b)) (g.map b) :=
        hY.isStronglyCartesian (g.map b)
      apply Functor.IsStronglyCartesian.ext pY (pY.map (g.map b)) (g.map b)
        (pY.map (e.hom ≫ g.map c))
      calc
        (f.map a ≫ P.iso.hom) ≫ g.map b = α := by rw [Category.assoc, hab']
        _ = e.hom ≫ g.map β := hefac.symm
        _ = e.hom ≫ g.map (c ≫ b) := by rw [hcb]
        _ = (e.hom ≫ g.map c) ≫ g.map b := by rw [Functor.map_comp, Category.assoc]
    let χ : P₀ ⟶ P := TwoFibreProductOver.Hom.mk' a c hcbase hsquare
    exact ⟨StructuredArrow.homMk (CostructuredArrow.homMk χ hcb)
      (CostructuredArrow.hom_ext _ _ (Category.id_comp a))⟩
  have : Nonempty (w.StructuredArrowRightwards α) := ⟨z₀⟩
  exact zigzag_isConnected fun z₁ z₂ => Zigzag.of_inv_hom (hfrom z₁) (hfrom z₂)

/-- **Stacks 075B**: in a 2-cartesian square of categories fibred in groupoids, the canonical
base-change transformation `g⁻¹ f_* ⟶ f'_* (g')⁻¹` for presheaves is an isomorphism, naturally in
the presheaf. -/
@[stacks 075B]
theorem isIso_presheafRanBaseChange
    (pX : X ⥤ C) (pY' : Y' ⥤ C) (pY : Y ⥤ C)
    (f : X ⥤ Y) (g : Y' ⥤ Y)
    (hX : pX.IsFiberedInGroupoids) (hY' : pY'.IsFiberedInGroupoids)
    (hY : pY.IsFiberedInGroupoids)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pY')
    [∀ (F : Xᵒᵖ ⥤ Type t), f.op.HasPointwiseRightKanExtension F]
    [∀ (F : (TwoFibreProductOver pX pY' pY f g)ᵒᵖ ⥤ Type t),
      (TwoFibreProductOver.snd pX pY' pY f g).op.HasPointwiseRightKanExtension F] :
    IsIso ((TwoSquare.mk
      (TwoFibreProductOver.fst pX pY' pY f g)
      (TwoFibreProductOver.snd pX pY' pY f g) f g
      (TwoFibreProductOver.psiIso pX pY' pY f g).hom).op.ranBaseChange
        (D := Type t)) :=
  let w := TwoSquare.mk
    (TwoFibreProductOver.fst pX pY' pY f g)
    (TwoFibreProductOver.snd pX pY' pY f g) f g
    (TwoFibreProductOver.psiIso pX pY' pY f g).hom
  let : w.GuitartExact :=
    guitartExact_twoFibreProductSquare pX pY' pY f g hX hY' hY hf hg
  let : w.op.GuitartExact := inferInstance
  by infer_instance

end CategoryTheory.TwoFibreProductOver

end
