module

public import StacksFrontier.CategoryTheory.FiberedInSets.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInSetoids.TwoFibreProduct

/-!
# The 2-fibre product of categories fibred in sets (Stacks 0047)

Stacks Tag `0047` (Lemma 4.38.4): the 2-category of categories fibred in sets over a base
category `𝒞` has 2-fibre products, and more precisely the 2-fibre product of Stacks `0040`
returns a category fibred in sets when its three inputs are fibred in sets.

## Main results

* `CategoryTheory.Functor.IsFiberedInSets.twoFibreProd`: Stacks 0047.

## Implementation notes

The 2-fibre product used is the explicit one *over `𝒞`*, `CategoryTheory.TwoFibreProd`, built
for Stacks `04SB` in `StacksFrontier/CategoryTheory/FiberedInSetoids/TwoFibreProduct.lean`: its
objects are quadruples `(U, x, y, f)` with `x` over `U` in `𝒳`, `y` over `U` in `𝒴` and `f :
F(x) ⟶ G(y)` an isomorphism of `𝒮` lying over `𝟙 U`. Mathlib's absolute
`CategoryTheory.Limits.CategoricalPullback` will not do here: it imposes no condition on the
comparison isomorphism, and its structure functor is *not* fibred in sets even when all three
inputs are — a second object isomorphic to the lifted one in `𝒴`, over the same object of `𝒞`,
gives a second lift.

Fibredness in sets is characterised (Stacks `0043`, `Functor.isFiberedInSets_iff`) as being
fibred in groupoids with discrete fibres, so it suffices to add discreteness of the fibres to
what Stacks `04SB` already proves for setoids: `TwoFibreProd.proj_isFiberedInGroupoids` gives
the fibredness in groupoids and `TwoFibreProd.proj_fiber_isThin` the thinness. Discreteness is
the extra step, and it is again componentwise: a morphism of a fibre of the 2-fibre product has
both of its components lying over an identity, so discreteness of the fibres of `pX` and `pY`
identifies the two components, and thinness of the fibres of `pS` — used here, unlike in
Stacks `04SB` — identifies the two comparison isomorphisms.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ u₁ v u w t s

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]
variable {𝒳 : Type u} [Category.{v} 𝒳] {𝒴 : Type w} [Category.{t} 𝒴]
variable {𝒮 : Type s} [Category.{v₁} 𝒮]

/-- A category fibred in sets is a category fibred in setoids: it is fibred in groupoids
(Stacks `0043`) and its fibres, being discrete, are in particular thin. -/
lemma Functor.IsFiberedInSets.isFiberedInSetoids (p : 𝒳 ⥤ 𝒞) [p.IsFiberedInSets] :
    p.IsFiberedInSetoids where
  isFiberedInGroupoids := Functor.IsFiberedInSets.isFiberedInGroupoids p
  fiber_isThin _ _ _ := inferInstance

variable (pX : 𝒳 ⥤ 𝒞) (pY : 𝒴 ⥤ 𝒞) (pS : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

namespace TwoFibreProd

variable {pX pY pS F G}

/-- Two objects of the 2-fibre product over `𝒞` are equal as soon as their base objects, their
`𝒳`- and `𝒴`-components and their comparison morphisms are; the remaining fields are
propositions. -/
lemma ext_of {P Q : TwoFibreProd pX pY pS F G} (hb : P.base = Q.base) (hx : P.x = Q.x)
    (hy : P.y = Q.y)
    (hf : ∀ (h₁ : F.obj P.x = F.obj Q.x) (h₂ : G.obj P.y = G.obj Q.y),
      P.f = eqToHom h₁ ≫ Q.f ≫ eqToHom h₂.symm) : P = Q := by
  obtain ⟨b, x, y, hxb, hyb, hFb, hGb, f, hi, ho⟩ := P
  obtain ⟨b', x', y', hxb', hyb', hFb', hGb', f', hi', ho'⟩ := Q
  subst hb hx hy
  have hff : f = f' := by simpa using hf rfl rfl
  subst hff
  rfl

/-- The source and target of a morphism lying over an identity are equal in a category fibred in
sets. -/
private lemma eq_of_isHomLift_id {𝒵 : Type*} [Category 𝒵] (p : 𝒵 ⥤ 𝒞) [p.IsFiberedInSets]
    {U : 𝒞} {a b : 𝒵} (φ : a ⟶ b) [p.IsHomLift (𝟙 U) φ] : a = b :=
  haveI := IsHomLift.id (p := p) (IsHomLift.codomain_eq p (𝟙 U) φ)
  (Functor.IsFiberedInSets.eq_of_isHomLift p (𝟙 U) φ (𝟙 b)).1

/-- Both components of a morphism of a fibre of the structure functor of the 2-fibre product
lie over the identity: for the `𝒳`-component this is the definition of `proj`, and for the
`𝒴`-component it then follows from the compatibility of the two components on bases. -/
lemma isHomLift_of_fiber_hom {U : 𝒞} {P Q : (TwoFibreProd.proj pX pY pS F G).Fiber U}
    (m : P ⟶ Q) :
    pX.IsHomLift (𝟙 U) m.1.a ∧ pY.IsHomLift (𝟙 U) m.1.b := by
  have hxP : pX.obj P.1.x = U := P.1.hx.trans P.2
  have hxQ : pX.obj Q.1.x = U := Q.1.hx.trans Q.2
  have hyP : pY.obj P.1.y = U := P.1.hy.trans P.2
  have hyQ : pY.obj Q.1.y = U := Q.1.hy.trans Q.2
  -- `Functor.Fiber` spells its defining equation with `proj.obj`; restate it with `base`, so
  -- that the `eqToHom` chains below are composable chains of objects `simp` can collapse.
  have hbP : P.1.base = U := P.2
  have hbQ : Q.1.base = U := Q.2
  have := m.2
  have hfac : eqToHom P.1.hx.symm ≫ pX.map m.1.a ≫ eqToHom Q.1.hx
      = eqToHom hbP ≫ 𝟙 U ≫ eqToHom hbQ.symm :=
    IsHomLift.fac' (TwoFibreProd.proj pX pY pS F G) (𝟙 U) m.1
  have ha : pX.map m.1.a = eqToHom hxP ≫ 𝟙 U ≫ eqToHom hxQ.symm := by
    simpa using congrArg (fun c : P.1.base ⟶ Q.1.base ↦
      eqToHom P.1.hx ≫ c ≫ eqToHom Q.1.hx.symm) hfac
  refine ⟨IsHomLift.of_fac' pX (𝟙 U) m.1.a hxP hxQ ha,
    IsHomLift.of_fac' pY (𝟙 U) m.1.b hyP hyQ ?_⟩
  have hb := congrArg (fun c : P.1.base ⟶ Q.1.base ↦
    eqToHom P.1.hy ≫ c ≫ eqToHom Q.1.hy.symm) m.1.base_compat.symm
  rw [ha] at hb
  simpa using hb

/-- Every fibre of the structure functor of the 2-fibre product over `𝒞` of three categories
fibred in sets is discrete. Thinness is Stacks `04SB`; that a morphism of a fibre forces its
source and target to be equal is checked componentwise, the comparison isomorphisms being
identified by thinness of the fibres of `pS`. -/
lemma proj_fiber_isDiscrete [pX.IsFiberedInSets] [pY.IsFiberedInSets] [pS.IsFiberedInSets]
    (U : 𝒞) : IsDiscrete ((TwoFibreProd.proj pX pY pS F G).Fiber U) where
  subsingleton := TwoFibreProd.proj_fiber_isThin pX pY pS F G
    (Functor.IsFiberedInSets.isFiberedInSetoids pX).fiber_isThin
    (Functor.IsFiberedInSets.isFiberedInSetoids pY).fiber_isThin U
  eq_of_hom {P Q} m := by
    obtain ⟨hlifta, hliftb⟩ := isHomLift_of_fiber_hom m
    have hbP : P.1.base = U := P.2
    have hbQ : Q.1.base = U := Q.2
    -- the two `𝒳`-components, resp. `𝒴`-components, agree: the fibres of `pX`, `pY` at `U`
    -- are discrete
    refine Subtype.ext (TwoFibreProd.ext_of (hbP.trans hbQ.symm)
      (eq_of_isHomLift_id (U := U) pX m.1.a) (eq_of_isHomLift_id (U := U) pY m.1.b) fun h₁ h₂ ↦ ?_)
    -- both comparison morphisms lie over `𝟙 U`, and the fibre of `pS` at `U` is thin
    have hFP : pS.obj (F.obj P.1.x) = U := P.1.hFx.trans hbP
    have hGP : pS.obj (G.obj P.1.y) = U := P.1.hGy.trans hbP
    have k₁ : pS.IsHomLift (𝟙 U) P.1.f :=
      IsHomLift.of_fac' pS (𝟙 U) P.1.f hFP hGP (by simp [P.1.f_over])
    have k₂ : pS.IsHomLift (𝟙 U) (eqToHom h₁ ≫ Q.1.f ≫ eqToHom h₂.symm) :=
      IsHomLift.of_fac' pS (𝟙 U) _ hFP hGP (by
        simp [Q.1.f_over, eqToHom_map])
    have := k₁
    have := k₂
    exact congrArg Subtype.val
      (Subsingleton.elim (Functor.Fiber.homMk pS U P.1.f) (Functor.Fiber.homMk pS U _))

end TwoFibreProd

/-- **Stacks 0047 (Lemma 4.38.4).** The 2-category of categories fibred in sets over `𝒞` has
2-fibre products: if `𝒳`, `𝒴`, `𝒮` are fibred in sets over `𝒞` and `F : 𝒳 ⥤ 𝒮`, `G : 𝒴 ⥤ 𝒮`
are 1-morphisms over `𝒞`, then the 2-fibre product `𝒳 ×_𝒮 𝒴` of Stacks `0040`, with its
structure functor, is again fibred in sets over `𝒞`. -/
@[stacks 0047]
theorem Functor.IsFiberedInSets.twoFibreProd
    [pX.IsFiberedInSets] [pY.IsFiberedInSets] [pS.IsFiberedInSets]
    (hF : F ⋙ pS = pX) (hG : G ⋙ pS = pY) :
    (TwoFibreProd.proj pX pY pS F G).IsFiberedInSets :=
  (Functor.isFiberedInSets_iff _).2
    ⟨TwoFibreProd.proj_isFiberedInGroupoids pX pY pS F G
      (Functor.IsFiberedInSets.isFiberedInGroupoids pX)
      (Functor.IsFiberedInSets.isFiberedInGroupoids pY)
      (Functor.IsFiberedInSets.isFiberedInGroupoids pS) hF hG,
    fun U ↦ TwoFibreProd.proj_fiber_isDiscrete (pX := pX) (pY := pY) (pS := pS) (F := F)
      (G := G) U⟩

end CategoryTheory
