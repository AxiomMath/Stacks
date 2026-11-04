module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack
import StacksCore.Tactic.EgaSgaAttribute

/-! # A fully faithful 1-morphism with vertical preimages is an equivalence over the base

Let `p : 𝒳 ⥤ 𝒞` and `q : 𝒴 ⥤ 𝒞` be categories over `𝒞` and let `F : 𝒳 ⥤ 𝒴` be a functor
over `𝒞`, that is `F ⋙ q = p`. If `F` is fully faithful and every object `y` of `𝒴` admits
an object `o` of `𝒳` over `q.obj y` together with an isomorphism `y ≅ F o` lying over an
identity, then `F` is an equivalence over `𝒞`: its quasi-inverse is again strictly a functor
over `𝒞`, and the unit and counit are vertical.

## Main results

* `CategoryTheory.Functor.isEquivalenceOver_of_exists_vertical_iso`, the construction of the
  equivalence over `𝒞` from the choice data;
* `CategoryTheory.Functor.exists_vertical_iso_of_fiber_essSurj`, the choice data from
  essential surjectivity of the induced functors on fibres;
* `CategoryTheory.Functor.fiber_essSurj_of_isEquivalenceOver`, the converse: an equivalence
  over `𝒞` induces essentially surjective functors on fibres.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴]

/-- The choice data of a vertical preimage: for every object `y` of `𝒴` an object of `𝒳` over
`q.obj y` and an isomorphism `y ≅ F o` lying over the identity of `q.obj y`. -/
def HasVerticalPreimages (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴) : Prop :=
  ∀ y : 𝒴, ∃ (o : 𝒳) (_ : p.obj o = q.obj y) (α : y ≅ F.obj o),
    q.IsHomLift (𝟙 (q.obj y)) α.hom

/-- A fully faithful functor over `𝒞` admitting vertical preimages is an equivalence over
`𝒞`. -/
noncomputable def isEquivalenceOver_of_exists_vertical_iso {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞}
    {F : 𝒳 ⥤ 𝒴} (hF : F ⋙ q = p) [F.Full] [F.Faithful]
    (hch : HasVerticalPreimages p q F) :
    IsEquivalenceOver p q F := by
  choose G₀ hG₀ho α hαlift using hch
  let hFff : F.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful F
  let inv : 𝒴 ⥤ 𝒳 :=
    { obj := G₀
      map := fun {y y'} g => hFff.preimage ((α y).inv ≫ g ≫ (α y').hom)
      map_id := fun y => by
        apply F.map_injective
        rw [hFff.map_preimage]; simp
      map_comp := fun {y y' y''} g h => by
        apply F.map_injective
        rw [F.map_comp, hFff.map_preimage, hFff.map_preimage, hFff.map_preimage]
        simp }
  have hαho : ∀ y : 𝒴, q.obj y = q.obj (F.obj (G₀ y)) := by
    intro y; rw [← hG₀ho, ← hF]; rfl
  have hαmaphom : ∀ y : 𝒴, q.map (α y).hom = eqToHom (hαho y) := fun y ↦
    ((IsHomLift.id_iff_exists_eqToHom q (α y).hom).1 (hαlift y)).choose_spec
  have hαmapinv : ∀ y : 𝒴, q.map (α y).inv = eqToHom (hαho y).symm := fun y ↦ by
    rw [← cancel_mono (q.map (α y).hom), ← q.map_comp, hαmaphom]
    simp
  have hinvp : inv ⋙ p = q := by
    refine CategoryTheory.Functor.ext (fun y => hG₀ho y) ?_
    intro y y' g
    rw [Functor.comp_map]
    have hmap : inv.map g = hFff.preimage ((α y).inv ≫ g ≫ (α y').hom) := rfl
    rw [map_eq_of_comp_eq p q F hF (inv.map g), hmap, hFff.map_preimage,
      q.map_comp, q.map_comp, hαmapinv, hαmaphom]
    simp
  have hFinvmap : ∀ {y y' : 𝒴} (g : y ⟶ y'),
      F.map (inv.map g) = (α y).inv ≫ g ≫ (α y').hom := fun _ ↦ hFff.map_preimage _
  let ε : inv ⋙ F ≅ 𝟭 𝒴 := NatIso.ofComponents (fun y => (α y).symm) (by
    intro y y' g
    simp [hFinvmap g])
  let θ : ∀ x : 𝒳, x ≅ G₀ (F.obj x) := fun x => hFff.preimageIso (α (F.obj x))
  have hFθinv : ∀ x : 𝒳, F.map (θ x).inv = (α (F.obj x)).inv := by
    intro x; simp [θ, Functor.FullyFaithful.preimageIso]
  let η : F ⋙ inv ≅ 𝟭 𝒳 := NatIso.ofComponents (fun x => (θ x).symm) (by
    intro x y φ
    apply F.map_injective
    simp [hFinvmap, hFθinv])
  refine
    { inv := inv
      inv_over := hinvp
      unitIso := η
      counitIso := ε
      unit_vertical := ?_
      counit_vertical := ?_ }
  · intro x
    have happ : η.hom.app x = (θ x).inv := by simp [η, NatIso.ofComponents]
    rw [happ]
    have hpx : p.obj x = p.obj ((F ⋙ inv).obj x) := by
      rw [Functor.comp_obj, hG₀ho (F.obj x)]
      exact (Functor.congr_obj hF x).symm
    refine IsHomLift.of_fac' p (𝟙 (p.obj ((F ⋙ inv).obj x))) (θ x).inv rfl hpx ?_
    rw [map_eq_of_comp_eq p q F hF (θ x).inv, hFθinv, hαmapinv (F.obj x)]
    simp
  · intro y
    have happ : ε.hom.app y = (α y).inv := by simp [ε, NatIso.ofComponents]
    rw [happ]
    refine IsHomLift.of_fac' q (𝟙 (q.obj ((inv ⋙ F).obj y))) (α y).inv rfl (hαho y) ?_
    simp [hαmapinv y]

-- The chosen preimage of an object of a fibre and the inclusion of a fibre are semireducible, so
-- the endpoints of the composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false in
/-- If the functors induced by `F` on the fibres are essentially surjective, then `F` has
vertical preimages. -/
theorem exists_vertical_iso_of_fiber_essSurj {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴}
    (hF : F ⋙ q = p) (hess : ∀ U : 𝒞, (Fiber.mapOfComp p q F hF U).EssSurj) :
    HasVerticalPreimages p q F := by
  intro y
  set U : 𝒞 := q.obj y with hU
  set yf : q.Fiber U := Fiber.mk (p := q) (a := y) rfl with hyf
  have := hess U
  set obar : p.Fiber U := (Fiber.mapOfComp p q F hF U).objPreimage yf with hobar
  set t : (Fiber.mapOfComp p q F hF U).obj obar ≅ yf :=
    (Fiber.mapOfComp p q F hF U).objObjPreimageIso yf with ht
  set tI : Fiber.fiberInclusion.obj yf
      ≅ Fiber.fiberInclusion.obj ((Fiber.mapOfComp p q F hF U).obj obar) :=
    Fiber.fiberInclusion.mapIso t.symm with htI
  have hcomp := Fiber.mapOfComp_comp_fiberInclusion p q F hF U
  have hsrc : Fiber.fiberInclusion.obj ((Fiber.mapOfComp p q F hF U).obj obar)
      = F.obj (Fiber.fiberInclusion.obj obar) := Functor.congr_obj hcomp obar
  have htgt : Fiber.fiberInclusion.obj yf = y := rfl
  refine ⟨Fiber.fiberInclusion.obj obar, obar.2, eqToIso htgt.symm ≪≫ tI ≪≫ eqToIso hsrc, ?_⟩
  have hlifttI : q.IsHomLift (𝟙 U) tI.hom := by
    rw [htI]
    simp only [Functor.mapIso_hom]
    infer_instance
  have hFoU : q.obj (F.obj (Fiber.fiberInclusion.obj obar)) = U :=
    (Functor.congr_obj hF _).trans obar.2
  have hlift1 : q.IsHomLift (𝟙 U) (eqToHom htgt.symm) := IsHomLift.eqToHom_domain_lift_id _ rfl
  have hlift2 : q.IsHomLift (𝟙 U) (eqToHom hsrc) := IsHomLift.eqToHom_codomain_lift_id _ hFoU
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [show 𝟙 U = 𝟙 U ≫ 𝟙 U ≫ 𝟙 U by simp]
  infer_instance

/-- An equivalence over `𝒞` induces an essentially surjective functor on every fibre. -/
@[sga "1 VI 4.2" "(i)"]
theorem fiber_essSurj_of_isEquivalenceOver {p : 𝒳 ⥤ 𝒞} {q : 𝒴 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒴}
    (hF : F ⋙ q = p) (E : IsEquivalenceOver p q F) (U : 𝒞) :
    (Fiber.mapOfComp p q F hF U).EssSurj := by
  refine ⟨fun yf => ?_⟩
  have hoU : p.obj (E.inv.obj yf.1) = U := (Functor.congr_obj E.inv_over yf.1).trans yf.2
  refine ⟨Fiber.mk (p := p) hoU, ⟨?_⟩⟩
  have hlift : q.IsHomLift (𝟙 U) (E.counitIso.hom.app yf.1) := by
    obtain ⟨he, hmap⟩ :=
      (IsHomLift.id_iff_exists_eqToHom q (E.counitIso.hom.app yf.1)).1 (E.counit_vertical yf.1)
    refine IsHomLift.of_fac' q (𝟙 U) (E.counitIso.hom.app yf.1)
      ((Functor.congr_obj hF _).trans hoU) yf.2 ?_
    simp [hmap]
  exact Fiber.isoMk (p := q) (Iso.app E.counitIso yf.1) hlift

end CategoryTheory.Functor
