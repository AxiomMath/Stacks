module

public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute

/-!
# Morphisms out of a fibre of the Grothendieck construction

Let `F : A ⥤ Cat` and let `Grothendieck.ι F a : F.obj a ⥤ Grothendieck F` be the inclusion
of the fibre over `a`. A morphism `⟨a, V⟩ ⟶ ⟨b, U⟩` of `Grothendieck F` is a pair consisting
of a base arrow `f : a ⟶ b` and a fibre arrow `(F.map f).obj V ⟶ U`, and precomposing it
with the image under `ι F a` of an arrow of `F.obj a` leaves the base arrow unchanged. So
the presheaf `V ↦ (⟨a, V⟩ ⟶ ⟨b, U⟩)` on `F.obj a` is the **coproduct**, over the base arrows
`f : a ⟶ b`, of the presheaves `V ↦ ((F.map f).obj V ⟶ U)`.

This is the combinatorial content of the direct-sum formula of Stacks 09WG (3) and (6) in
case (B) of Stacks 09WE, where the total site of a simplicial site is the Grothendieck
construction on a simplicial object of `Cat`: the base arrows `op m ⟶ op n` are exactly the
simplex maps `n ⟶ m` indexing the sum, and `V ↦ ((F.map f).obj V ⟶ U)` is the presheaf whose
`Hom(-, P)` computes the direct image of `P` along the transition belonging to `f`.

## Main definitions

* `CategoryTheory.Grothendieck.ιHomPresheaf`: the presheaf `V ↦ (⟨a, V⟩ ⟶ ⟨b, U⟩)`, namely
  `(ι F a).op ⋙ yoneda.obj ⟨b, U⟩`.
* `CategoryTheory.Grothendieck.transitionHomPresheaf`: one summand, `V ↦ ((F.map f).obj V ⟶ U)`.
* `CategoryTheory.Grothendieck.ιHomCofan`: the cofan assembling the summands into
  `ιHomPresheaf`, whose leg at `f` sends a fibre arrow `g` to the morphism `⟨f, g⟩`.

## Main results

* `CategoryTheory.Grothendieck.mk_map_comp`: precomposing `h : ⟨a, V⟩ ⟶ Y` with the arrow of
  `Grothendieck F` that `ι F a` assigns to `k : V' ⟶ V` gives `⟨h.base, (F.map h.base).map k ≫
  h.fiber⟩`. This is the lemma the decomposition rests on: the base arrow is unchanged, so
  the index of the summand is constant along the presheaf's restriction maps.
* `CategoryTheory.Grothendieck.ιHomCofanIsColimit`: `ιHomCofan` is a colimit, so
  `ιHomPresheaf` is the coproduct of the `transitionHomPresheaf`.

## Implementation notes

`mk_map_comp` is an equality of morphisms of `Grothendieck F` whose base arrows are
`𝟙 a ≫ h.base` and `h.base`: equal, but not definitionally, which is why the statement is
needed at all. Three points about its proof, each of which cost a compile cycle:

* the base component must be discharged by `(comp_base _ _).trans (Category.id_comp _)` and
  not by `Category.id_comp _` alone. The latter elaborates only after unfolding
  `Grothendieck.comp`, which is semireducible, so the resulting `Grothendieck.ext` term is
  not type-correct at `implicit` transparency and every later `simp` or `rw` silently makes
  no progress — the symptom being `Functor.map_comp` failing to fire on a visible
  `Φ.map (u ≫ v)`;
* the source object must be spelled `Grothendieck.mk a V`, not `(ι F a).obj V`. With the
  latter, `h.base : ((ι F a).obj V).base ⟶ Y.base` and `F.map h.base` carries a category
  instance on `F.obj ((ι F a).obj V).base`, which `simp` does not identify with the one on
  `F.obj a`;
* the comparison `ιHomPresheafIsoSigma` with the hom presheaf, whose objects *are* spelled
  through `ι`, therefore cannot be proved by `simp`; it is a single `congrArg` applied to
  `mk_map_comp`, which goes through because `exact` checks definitional equality at default
  transparency.

The explicit sigma-type presheaf `ιHomSigmaPresheaf` is interposed because the coproduct
structure is visible on it: its restriction maps fix the first component on the nose, so the
cofan legs are natural by construction and the colimit property is a two-line computation.

The fibre morphism universe of `F` is written `max v₁ w`, with `v₁` the morphism universe of
`A`. That is no loss in the intended application, where `A = Δᵒᵖ` has `v₁ = 0`, and it is
what puts the hom-sets of `Grothendieck F` and of the fibres in one universe, so that the
summands and the total presheaf are presheaves of the same kind.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 09WD](https://stacks.math.columbia.edu/tag/09WD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u₁ v₁ u₂

namespace CategoryTheory.Grothendieck

variable {A : Type u₁} [Category.{v₁} A] (F : A ⥤ Cat.{max v₁ w, u₂})

/-- Precomposing a morphism out of the fibre over `a` with the arrow of `Grothendieck F`
belonging to a fibre arrow `k` leaves the base arrow unchanged, and acts on the fibre arrow
through the transition functor of that base arrow. -/
public theorem mk_map_comp {a : A} {V V' : F.obj a} (k : V' ⟶ V) {Y : Grothendieck F}
    (h : (Grothendieck.mk a V : Grothendieck F) ⟶ Y) :
    ({ base := 𝟙 a, fiber := eqToHom (by simp) ≫ k } :
        (Grothendieck.mk a V' : Grothendieck F) ⟶ Grothendieck.mk a V) ≫ h =
      { base := h.base, fiber := (F.map h.base).toFunctor.map k ≫ h.fiber } := by
  refine Grothendieck.ext _ _
    ((Grothendieck.comp_base _ _).trans (Category.id_comp _)) ?_
  simp only [Grothendieck.comp_fiber, Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- The arrow of `Grothendieck F` that `ι F a` assigns to a fibre arrow. -/
public theorem ι_map_eq_mk {a : A} {V V' : F.obj a} (k : V' ⟶ V) :
    (Grothendieck.ι F a).map k =
      ({ base := 𝟙 a, fiber := eqToHom (by simp) ≫ k } :
        (Grothendieck.mk a V' : Grothendieck F) ⟶ Grothendieck.mk a V) :=
  rfl

variable (a b : A) (U : F.obj b)

/-- The presheaf on the fibre over `a` of morphisms to a fixed object `⟨b, U⟩`. -/
public abbrev ιHomPresheaf : (F.obj a)ᵒᵖ ⥤ Type (max v₁ w) :=
  (Grothendieck.ι F a).op ⋙ yoneda.obj (Grothendieck.mk b U)

/-- The presheaf of fibre morphisms along a fixed base arrow: one summand of
`ιHomPresheaf`. -/
public abbrev transitionHomPresheaf (f : a ⟶ b) : (F.obj a)ᵒᵖ ⥤ Type (max v₁ w) :=
  (F.map f).toFunctor.op ⋙ yoneda.obj U

/-- The presheaf `V ↦ Σ f : a ⟶ b, ((F.map f).obj V ⟶ U)`, on which the decomposition of
`ιHomPresheaf` is visible, because its restriction maps fix the base arrow. -/
public def ιHomSigmaPresheaf : (F.obj a)ᵒᵖ ⥤ Type (max v₁ w) where
  obj V := Σ f : a ⟶ b, ((F.map f).toFunctor.obj V.unop ⟶ U)
  map {V V'} k := ↾fun p => ⟨p.1, (F.map p.1).toFunctor.map k.unop ≫ p.2⟩
  map_id := by intro V; ext p <;> simp
  map_comp := by intro V V' V'' k l; ext p <;> simp

/-- The cofan on the summands with point the sigma-type presheaf. -/
public def ιHomSigmaCofan : Cofan (fun f : a ⟶ b => transitionHomPresheaf F a b U f) :=
  Cofan.mk (ιHomSigmaPresheaf F a b U) fun f => { app := fun _ => ↾fun g => ⟨f, g⟩ }

/-- The sigma-type presheaf is the coproduct of the summands. -/
public def ιHomSigmaCofanIsColimit : IsColimit (ιHomSigmaCofan F a b U) :=
  Cofan.IsColimit.mk _
    (fun t =>
      { app := fun V => ↾fun p => (t.inj p.1).app V p.2
        naturality := fun V V' k => by
          ext p
          exact NatTrans.naturality_apply (t.inj p.1) k p.2 })
    (fun _ _ => rfl)
    (fun t m hm => by
      refine NatTrans.ext (funext fun V => ?_)
      ext p
      obtain ⟨f, g⟩ : Σ f : a ⟶ b, ((F.map f).toFunctor.obj V.unop ⟶ U) := p
      exact congrArg (fun φ : transitionHomPresheaf F a b U f ⟶ t.pt => φ.app V g) (hm f))

/-- The presheaf of morphisms out of the fibre over `a` is the sigma-type presheaf. -/
public def ιHomPresheafIsoSigma :
    ιHomPresheaf F a b U ≅ ιHomSigmaPresheaf F a b U :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun h => ⟨h.base, h.fiber⟩
        invFun := fun p => { base := p.1, fiber := p.2 }
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl })
    (fun {_ V'} k => by
      ext h
      exact congrArg
        (fun m : (Grothendieck.ι F a).obj V'.unop ⟶ Grothendieck.mk b U =>
          (⟨m.base, m.fiber⟩ : Σ f : a ⟶ b, ((F.map f).toFunctor.obj V'.unop ⟶ U)))
        (mk_map_comp F k.unop h))

/-- The cofan on the summands with point the presheaf of morphisms out of the fibre: its leg
at a base arrow `f` sends a fibre arrow `g` to the morphism `⟨f, g⟩`. -/
public def ιHomCofan : Cofan (fun f : a ⟶ b => transitionHomPresheaf F a b U f) :=
  Cofan.mk (ιHomPresheaf F a b U)
    fun f =>
      { app := fun _ => ↾fun g => { base := f, fiber := g }
        naturality := fun X _ k => by
          ext g
          exact (mk_map_comp F k.unop
            ({ base := f, fiber := g } :
              (Grothendieck.mk a X.unop : Grothendieck F) ⟶ Grothendieck.mk b U)).symm }

/-- **The decomposition.** The presheaf `V ↦ (⟨a, V⟩ ⟶ ⟨b, U⟩)` on the fibre `F.obj a` is the
coproduct, over the base arrows `f : a ⟶ b`, of the presheaves `V ↦ ((F.map f).obj V ⟶ U)`. -/
public def ιHomCofanIsColimit : IsColimit (ιHomCofan F a b U) :=
  IsColimit.ofIsoColimit (ιHomSigmaCofanIsColimit F a b U)
    (Cocone.ext (ιHomPresheafIsoSigma F a b U).symm
      (by rintro ⟨f⟩; exact NatTrans.ext (funext fun _ => rfl)))

end CategoryTheory.Grothendieck

end
