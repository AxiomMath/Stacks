module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks

/-!
# Categories fibred in groupoids and their pseudofunctor of fibres (Stacks 003V)

Stacks Lemma 003V says, for a functor `p : 𝒳 ⥤ 𝒮`:

* `p` is fibred in groupoids if and only if `p` is a fibred category all of whose fibres are
  groupoids;
* in that case every morphism of `𝒳` is strongly cartesian;
* in that case, for any choice of morphisms `f^* x ⟶ x` lying over `f`, one for every
  `f : V ⟶ U` and every `x` over `U`, the data `(U ↦ 𝒳_U, f ↦ f^*, α_{g,f}, α_U)` of Stacks 02XO
  form a pseudofunctor from `𝒮ᵒᵖ` to the `(2, 1)`-category of groupoids.

The first two items are proved in `StacksCore/CategoryTheory/FiberedInGroupoidsEquiv.lean`. This file
supplies the third. For an arbitrary choice of pullbacks `c` (Stacks 02XN) of a fibred category,
`CategoryTheory.Functor.ChoiceOfPullbacks.pseudofunctor` is the pseudofunctor of Stacks 02XO (3):
its value at `U` is the fibre `𝒳_U`, its value at `f` is the pullback functor `f^*` of `c`, and its
unitor and compositor are the canonical isomorphisms `α_U` and `α_{g,f}` of Stacks 02XO (1), (2),
characterised by their compatibility with the chosen lifts
(`ChoiceOfPullbacks.pseudofunctor_mapId_hom_app` and
`ChoiceOfPullbacks.pseudofunctor_mapComp_hom_app_fac`). For a category fibred in groupoids any
morphism lying over `f` is strongly cartesian, so any choice of lifts is a choice of pullbacks
(`ChoiceOfPullbacks.ofIsFiberedInGroupoids`), and the values of its pseudofunctor are groupoids.

The `(2, 1)`-category of groupoids is the full sub-2-category of `Cat` on the groupoids: a natural
transformation between functors into a groupoid is automatically invertible. So a pseudofunctor
`LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat` all of whose values are groupoids is a pseudofunctor into the
`(2, 1)`-category of groupoids; this is how the statement is phrased.

## Main definitions

* `CategoryTheory.Functor.ChoiceOfPullbacks.pseudofunctor`: the pseudofunctor of Stacks 02XO (3)
  attached to an arbitrary choice of pullbacks.
* `CategoryTheory.Functor.ChoiceOfPullbacks.ofIsFiberedInGroupoids`: in a category fibred in
  groupoids, a choice of lifts lying over the base morphisms is a choice of pullbacks.

## Main results

* `CategoryTheory.Functor.ChoiceOfPullbacks.existsUnique_compIso`: Stacks 02XO (1) as stated
  in the source, the existence and uniqueness of the isomorphism `α_{g,f}`.
* `CategoryTheory.Functor.isFiberedInGroupoids_iff_and_isStronglyCartesian_and_isGroupoid`:
  the complete statement of Stacks 003V.
-/

@[expose] public section

namespace CategoryTheory.Functor

open Opposite Bicategory

universe v₁ v₂ u₁ u₂

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

-- `Fiber` and `Fiber.fiberInclusion` are plain `def`s, so goals mentioning an object of a fibre or
-- its image in `𝒳` are not type-correct at `implicit` transparency and `rw`/`simp` refuse them.
attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

namespace ChoiceOfPullbacks

variable {p : 𝒳 ⥤ 𝒮} (c : p.ChoiceOfPullbacks)

/-! ### The comparison isomorphisms, indexed by a base morphism equal to a composite

The pseudofunctor is indexed by the morphisms of `LocallyDiscrete 𝒮ᵒᵖ`, whose composites unfold
to composites in `𝒮` up to definitional equality, not syntactically. The comparisons below
therefore take the base morphism `k` together with a proof that it equals the identity,
respectively the composite, so that every lemma about them is stated with the very `k` that
occurs in the goals. -/

/-- The comparison `k^* x ≅ x` for a base morphism `k` equal to an identity: the chosen lift of
`k` at `x` regarded as an isomorphism of the fibre. -/
noncomputable def idIso {U : 𝒮} (k : U ⟶ U) (hk : k = 𝟙 U) (x : p.Fiber U) : c.obj k x ≅ x :=
  have : p.IsCartesian k (𝟙 x.1) := by
    subst hk
    have : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    infer_instance
  fiberIsoOfCartesian k (c.map k x) (𝟙 x.1) inferInstance this

/-- The comparison `k^* x ≅ x` is, in `𝒳`, the chosen lift of `k` at `x`. -/
lemma fiberInclusion_map_idIso_hom {U : 𝒮} (k : U ⟶ U) (hk : k = 𝟙 U) (x : p.Fiber U) :
    Fiber.fiberInclusion.map (c.idIso k hk x).hom = c.map k x := by
  have : p.IsCartesian k (𝟙 x.1) := by
    subst hk
    have : p.IsHomLift (𝟙 U) (𝟙 x.1) := IsHomLift.id x.2
    infer_instance
  exact (Category.comp_id _).symm.trans
    (fiberIsoOfCartesian_hom_fac k (c.map k x) (𝟙 x.1) inferInstance this)

/-- The composite of the chosen lifts of `g` and `f` is strongly cartesian over any `k` equal to
`g ≫ f`. -/
lemma isStronglyCartesian_map_comp_map {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (k : W ⟶ U)
    (hk : k = g ≫ f) (x : p.Fiber U) :
    p.IsStronglyCartesian k (c.map g (c.obj f x) ≫ c.map f x) := by
  subst hk
  infer_instance

/-- The comparison `k^* x ≅ g^* (f^* x)` for a base morphism `k` equal to `g ≫ f`: the two
objects carry strongly cartesian morphisms over `k` into `x`, the chosen lift of `k` and the
composite of the chosen lifts of `g` and of `f`. -/
noncomputable def compIso {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (k : W ⟶ U) (hk : k = g ≫ f)
    (x : p.Fiber U) : c.obj k x ≅ c.obj g (c.obj f x) :=
  have := c.isStronglyCartesian_map_comp_map g f k hk x
  fiberIsoOfCartesian k (c.map k x) (c.map g (c.obj f x) ≫ c.map f x) inferInstance
    inferInstance

/-- The comparison `k^* x ≅ g^* (f^* x)` carries the composite of the chosen lifts of `g` and `f`
to the chosen lift of `k`. -/
@[reassoc]
lemma compIso_hom_fac {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (k : W ⟶ U) (hk : k = g ≫ f)
    (x : p.Fiber U) :
    Fiber.fiberInclusion.map (c.compIso g f k hk x).hom ≫ c.map g (c.obj f x) ≫ c.map f x =
      c.map k x := by
  have := c.isStronglyCartesian_map_comp_map g f k hk x
  exact fiberIsoOfCartesian_hom_fac k (c.map k x) (c.map g (c.obj f x) ≫ c.map f x)
    inferInstance inferInstance

/-- The inverse comparison carries the chosen lift of `k` to the composite of the chosen lifts of
`g` and `f`. -/
@[reassoc]
lemma compIso_inv_fac {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (k : W ⟶ U) (hk : k = g ≫ f)
    (x : p.Fiber U) :
    Fiber.fiberInclusion.map (c.compIso g f k hk x).inv ≫ c.map k x =
      c.map g (c.obj f x) ≫ c.map f x := by
  rw [← c.compIso_hom_fac g f k hk x, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
    Functor.map_id, Category.id_comp]

/-- Transport of a chosen lift along an equality of base morphisms. -/
lemma eqToHom_comp_map {V U : 𝒮} {k k' : V ⟶ U} (e : k = k') (x : p.Fiber U)
    (h : Fiber.fiberInclusion.obj (c.obj k x) = Fiber.fiberInclusion.obj (c.obj k' x)) :
    eqToHom h ≫ c.map k' x = c.map k x := by
  subst e
  simp

/-- Naturality of `ChoiceOfPullbacks.idIso`. -/
lemma idIso_hom_naturality {U : 𝒮} (k : U ⟶ U) (hk : k = 𝟙 U) {x x' : p.Fiber U} (α : x ⟶ x') :
    c.homMap k α ≫ (c.idIso k hk x').hom = (c.idIso k hk x).hom ≫ α :=
  Fiber.hom_ext <| by
    rw [Functor.map_comp, Functor.map_comp, fiberInclusion_map_idIso_hom,
      fiberInclusion_map_idIso_hom, homMap_fac]

/-- Naturality of `ChoiceOfPullbacks.compIso`. -/
lemma compIso_hom_naturality {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) (k : W ⟶ U) (hk : k = g ≫ f)
    {x x' : p.Fiber U} (α : x ⟶ x') :
    c.homMap k α ≫ (c.compIso g f k hk x').hom =
      (c.compIso g f k hk x).hom ≫ c.homMap g (c.homMap f α) := by
  have := c.isStronglyCartesian_map_comp_map g f k hk x'
  refine fiber_hom_ext_of_cartesian k (c.map g (c.obj f x') ≫ c.map f x') inferInstance _ _ ?_
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, compIso_hom_fac, homMap_fac,
    Category.assoc, homMap_fac_assoc, homMap_fac, compIso_hom_fac_assoc]

/-! ### The pseudofunctor of a choice of pullbacks (Stacks 02XO) -/

/-- Object part: `U ↦ 𝒳_U`. -/
noncomputable abbrev pseudofunctorObj (U : LocallyDiscrete 𝒮ᵒᵖ) : Cat :=
  Cat.of (p.Fiber U.as.unop)

/-- 1-cell part: a morphism `φ` of `LocallyDiscrete 𝒮ᵒᵖ` goes to the pullback functor along
`φ.as.unop`. -/
noncomputable def pseudofunctorMap {U V : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) :
    pseudofunctorObj (p := p) U ⟶ pseudofunctorObj (p := p) V :=
  Cat.Hom.ofFunctor (c.pullbackFunctor φ.as.unop)

lemma pseudofunctorMap_obj {U V : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V)
    (x : pseudofunctorObj (p := p) U) :
    (c.pseudofunctorMap φ).toFunctor.obj x = c.obj φ.as.unop x := rfl

lemma pseudofunctorMap_map {U V : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V)
    {x x' : pseudofunctorObj (p := p) U} (α : x ⟶ x') :
    (c.pseudofunctorMap φ).toFunctor.map α = c.homMap φ.as.unop α := rfl

/-- The unitor `(𝟙 U)^* ≅ 𝟭`, the isomorphism `α_U` of Stacks 02XO (2). -/
noncomputable def pseudofunctorMapId (U : LocallyDiscrete 𝒮ᵒᵖ) :
    c.pseudofunctorMap (𝟙 U) ≅ 𝟙 (pseudofunctorObj (p := p) U) :=
  Cat.Hom.isoMk (NatIso.ofComponents (c.idIso (𝟙 U : U ⟶ U).as.unop rfl)
    fun α => c.idIso_hom_naturality _ rfl α)

/-- The compositor `(φ ≫ γ)^* ≅ φ^* ⋙ γ^*`, the isomorphism `α_{g,f}` of Stacks 02XO (1). -/
noncomputable def pseudofunctorMapComp {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W) :
    c.pseudofunctorMap (φ ≫ γ) ≅ c.pseudofunctorMap φ ≫ c.pseudofunctorMap γ :=
  Cat.Hom.isoMk (NatIso.ofComponents (c.compIso γ.as.unop φ.as.unop (φ ≫ γ).as.unop rfl)
    fun α => c.compIso_hom_naturality _ _ _ rfl α)

lemma pseudofunctorMapId_hom_app (U : LocallyDiscrete 𝒮ᵒᵖ) (x : pseudofunctorObj (p := p) U) :
    (c.pseudofunctorMapId U).hom.toNatTrans.app x = (c.idIso (𝟙 U : U ⟶ U).as.unop rfl x).hom := rfl

lemma pseudofunctorMapComp_hom_app {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W)
    (x : pseudofunctorObj (p := p) U) :
    (c.pseudofunctorMapComp φ γ).hom.toNatTrans.app x =
      (c.compIso γ.as.unop φ.as.unop (φ ≫ γ).as.unop rfl x).hom := rfl

lemma pseudofunctorMapComp_inv_app {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W)
    (x : pseudofunctorObj (p := p) U) :
    (c.pseudofunctorMapComp φ γ).inv.toNatTrans.app x =
      (c.compIso γ.as.unop φ.as.unop (φ ≫ γ).as.unop rfl x).inv := rfl

/-! ### The three coherences, componentwise in the fibres

Each coherence of the pseudofunctor is, at an object `X`, an equation between morphisms of a fibre
into a chosen pullback. Composing with the chosen (strongly cartesian) lift reduces it to the
defining triangles of the comparisons. The equations are stated here for base morphisms of `𝒮`,
with the composites recorded as hypotheses, so that they apply verbatim to the indices coming
from `LocallyDiscrete 𝒮ᵒᵖ`. -/

/-- Associativity of the comparisons `ChoiceOfPullbacks.compIso`, at an object `X`. -/
lemma compIso_assoc {U₀ U₁ U₂ U₃ : 𝒮} (f : U₁ ⟶ U₀) (g : U₂ ⟶ U₁) (h : U₃ ⟶ U₂)
    (fg : U₂ ⟶ U₀) (hfg : fg = g ≫ f) (gh : U₃ ⟶ U₁) (hgh : gh = h ≫ g) (k k' : U₃ ⟶ U₀)
    (hk : k = h ≫ fg) (hk' : k' = gh ≫ f) (X : p.Fiber U₀) (e : c.obj k X = c.obj k' X) :
    (c.compIso h fg k hk X).hom ≫ c.homMap h (c.compIso g f fg hfg X).hom ≫
        (c.compIso h g gh hgh (c.obj f X)).inv ≫ (c.compIso gh f k' hk' X).inv = eqToHom e := by
  refine fiber_hom_ext_of_cartesian k' (c.map k' X) inferInstance _ _ ?_
  have hkk : k = k' := by rw [hk, hk', hfg, hgh, Category.assoc]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, compIso_inv_fac, compIso_inv_fac_assoc, homMap_fac_assoc, compIso_hom_fac,
    compIso_hom_fac, CategoryTheory.eqToHom_map, eqToHom_comp_map c hkk]

/-- The left unit law of the comparisons, at an object `X`. -/
lemma compIso_idIso_left {V U : 𝒮} (g : V ⟶ U) (i : U ⟶ U) (hi : i = 𝟙 U) (k : V ⟶ U)
    (hk : k = g ≫ i) (X : p.Fiber U) (e : c.obj k X = c.obj g X) :
    (c.compIso g i k hk X).hom ≫ c.homMap g (c.idIso i hi X).hom = eqToHom e := by
  refine fiber_hom_ext_of_cartesian g (c.map g X) inferInstance _ _ ?_
  have hkg : k = g := by rw [hk, hi, Category.comp_id]
  rw [Functor.map_comp, Category.assoc, homMap_fac, fiberInclusion_map_idIso_hom,
    compIso_hom_fac, CategoryTheory.eqToHom_map, eqToHom_comp_map c hkg]

/-- The right unit law of the comparisons, at an object `X`. -/
lemma compIso_idIso_right {V U : 𝒮} (i : V ⟶ V) (hi : i = 𝟙 V) (f : V ⟶ U) (k : V ⟶ U)
    (hk : k = i ≫ f) (X : p.Fiber U) (e : c.obj k X = c.obj f X) :
    (c.compIso i f k hk X).hom ≫ (c.idIso i hi (c.obj f X)).hom = eqToHom e := by
  refine fiber_hom_ext_of_cartesian f (c.map f X) inferInstance _ _ ?_
  have hkf : k = f := by rw [hk, hi, Category.id_comp]
  rw [Functor.map_comp, Category.assoc, fiberInclusion_map_idIso_hom, compIso_hom_fac,
    CategoryTheory.eqToHom_map, eqToHom_comp_map c hkf]

/-- The associativity coherence of the pullback pseudofunctor of a choice of pullbacks. -/
lemma pseudofunctorMapComp_associator {b₀ b₁ b₂ b₃ : LocallyDiscrete 𝒮ᵒᵖ} (f : b₀ ⟶ b₁)
    (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    (c.pseudofunctorMapComp (f ≫ g) h).hom ≫
        (c.pseudofunctorMapComp f g).hom ▷ c.pseudofunctorMap h ≫
          (α_ (c.pseudofunctorMap f) (c.pseudofunctorMap g) (c.pseudofunctorMap h)).hom ≫
            c.pseudofunctorMap f ◁ (c.pseudofunctorMapComp g h).inv ≫
              (c.pseudofunctorMapComp f (g ≫ h)).inv =
      eqToHom (by rw [Category.assoc]) := by
  apply Cat.Hom₂.ext
  ext X
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app,
    Cat.associator_hom_app, Cat.Hom₂.eqToHom_toNatTrans, CategoryTheory.eqToHom_app,
    eqToHom_refl, Category.id_comp, pseudofunctorMapComp_hom_app, pseudofunctorMapComp_inv_app]
  exact c.compIso_assoc f.as.unop g.as.unop h.as.unop _ rfl _ rfl _ _ rfl rfl X _

/-- The left unitor coherence of the pullback pseudofunctor of a choice of pullbacks. -/
lemma pseudofunctorMapComp_left_unitor {b₀ b₁ : LocallyDiscrete 𝒮ᵒᵖ} (f : b₀ ⟶ b₁) :
    (c.pseudofunctorMapComp (𝟙 b₀) f).hom ≫
        (c.pseudofunctorMapId b₀).hom ▷ c.pseudofunctorMap f ≫
          (λ_ (c.pseudofunctorMap f)).hom =
      eqToHom (by rw [Category.id_comp]) := by
  apply Cat.Hom₂.ext
  ext X
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.leftUnitor_hom_app, CategoryTheory.eqToHom_app, eqToHom_refl, Category.comp_id,
    pseudofunctorMapComp_hom_app, pseudofunctorMapId_hom_app]
  exact c.compIso_idIso_left f.as.unop _ rfl _ rfl X _

/-- The right unitor coherence of the pullback pseudofunctor of a choice of pullbacks. -/
lemma pseudofunctorMapComp_right_unitor {b₀ b₁ : LocallyDiscrete 𝒮ᵒᵖ} (f : b₀ ⟶ b₁) :
    (c.pseudofunctorMapComp f (𝟙 b₁)).hom ≫
        c.pseudofunctorMap f ◁ (c.pseudofunctorMapId b₁).hom ≫
          (ρ_ (c.pseudofunctorMap f)).hom =
      eqToHom (by rw [Category.comp_id]) := by
  apply Cat.Hom₂.ext
  ext X
  simp only [Cat.Hom₂.comp_app, Cat.whiskerLeft_app, Cat.Hom₂.eqToHom_toNatTrans,
    Cat.rightUnitor_hom_app, CategoryTheory.eqToHom_app, eqToHom_refl,
    pseudofunctorMapComp_hom_app, pseudofunctorMapId_hom_app]
  refine (Category.assoc _ _ _).symm.trans ((Category.comp_id _).trans ?_)
  exact c.compIso_idIso_right _ rfl f.as.unop (f ≫ 𝟙 b₁).as.unop rfl X _

/-- **Stacks 02XO (3)**, for an arbitrary choice of pullbacks. The pseudofunctor
`𝒮ᵒᵖ ⥤ᵖ Cat` attached to a choice of pullbacks `c` of a fibred category: `U ↦ 𝒳_U`,
`f ↦ f^*` (the pullback functor of `c`), with unitor `α_U` and compositor `α_{g,f}` the canonical
isomorphisms of Stacks 02XO (1), (2). -/
@[stacks 02XO "(3), for an arbitrary choice of pullbacks"]
noncomputable def pseudofunctor : Pseudofunctor (LocallyDiscrete 𝒮ᵒᵖ) Cat :=
  pseudofunctorOfIsLocallyDiscrete
    (obj := pseudofunctorObj (p := p))
    (map := fun {_ _} φ => c.pseudofunctorMap φ)
    (mapId := fun U => c.pseudofunctorMapId U)
    (mapComp := fun {_ _ _} φ γ => c.pseudofunctorMapComp φ γ)
    (map₂_associator := fun {_ _ _ _} f g h => c.pseudofunctorMapComp_associator f g h)
    (map₂_left_unitor := fun {_ _} f => c.pseudofunctorMapComp_left_unitor f)
    (map₂_right_unitor := fun {_ _} f => c.pseudofunctorMapComp_right_unitor f)

/-- The value of `c.pseudofunctor` at `U` is the fibre `𝒳_U`. -/
lemma pseudofunctor_obj (U : 𝒮) : c.pseudofunctor.obj ⟨op U⟩ = Cat.of (p.Fiber U) := rfl

/-- The value of `c.pseudofunctor` at `f : V ⟶ U` is the pullback functor `f^*` of `c`. -/
lemma pseudofunctor_map {V U : 𝒮} (f : V ⟶ U) :
    (c.pseudofunctor.map (⟨f.op⟩ : (⟨op U⟩ : LocallyDiscrete 𝒮ᵒᵖ) ⟶ ⟨op V⟩)).toFunctor =
      c.pullbackFunctor f := rfl

/-- **Stacks 02XO (2).** The component at `x` of the unitor of `c.pseudofunctor` is, in `𝒳`, the
chosen lift of the identity at `x`. -/
@[stacks 02XO "(2), for an arbitrary choice of pullbacks"]
lemma pseudofunctor_mapId_hom_app (U : LocallyDiscrete 𝒮ᵒᵖ) (x : p.Fiber U.as.unop) :
    Fiber.fiberInclusion.map ((c.pseudofunctor.mapId U).hom.toNatTrans.app x) =
      c.map (𝟙 U.as.unop) x := by
  exact c.fiberInclusion_map_idIso_hom _ rfl x

/-- **Stacks 02XO (1).** The component at `x` of the compositor of `c.pseudofunctor` at `(φ, γ)`
makes the triangle with the chosen lifts commute: followed by the chosen lifts of `γ` and of `φ`,
it is the chosen lift of the composite. -/
@[stacks 02XO "(1), for an arbitrary choice of pullbacks"]
lemma pseudofunctor_mapComp_hom_app_fac {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V) (γ : V ⟶ W)
    (x : p.Fiber U.as.unop) :
    Fiber.fiberInclusion.map ((c.pseudofunctor.mapComp φ γ).hom.toNatTrans.app x) ≫
        c.map γ.as.unop (c.obj φ.as.unop x) ≫ c.map φ.as.unop x =
      c.map (φ ≫ γ).as.unop x := by
  exact c.compIso_hom_fac _ _ _ rfl x

/-- **Stacks 02XO (1), uniqueness.** The component at `x` of the compositor of `c.pseudofunctor` at
`(φ, γ)` is the unique morphism of the fibre making the triangle with the chosen lifts commute. -/
@[stacks 02XO "(1), uniqueness, for an arbitrary choice of pullbacks"]
lemma pseudofunctor_mapComp_hom_app_unique {U V W : LocallyDiscrete 𝒮ᵒᵖ} (φ : U ⟶ V)
    (γ : V ⟶ W) (x : p.Fiber U.as.unop)
    (θ : c.obj (φ ≫ γ).as.unop x ⟶ c.obj γ.as.unop (c.obj φ.as.unop x))
    (hθ : Fiber.fiberInclusion.map θ ≫ c.map γ.as.unop (c.obj φ.as.unop x) ≫
        c.map φ.as.unop x = c.map (φ ≫ γ).as.unop x) :
    θ = (c.pseudofunctor.mapComp φ γ).hom.toNatTrans.app x := by
  have := c.isStronglyCartesian_map_comp_map γ.as.unop φ.as.unop (φ ≫ γ).as.unop rfl x
  refine fiber_hom_ext_of_cartesian (φ ≫ γ).as.unop
    (c.map γ.as.unop (c.obj φ.as.unop x) ≫ c.map φ.as.unop x) inferInstance _ _ ?_
  rw [hθ]
  exact (c.pseudofunctor_mapComp_hom_app_fac φ γ x).symm

/-- **Stacks 02XO (1)**, as stated in the source. For composable `f : V ⟶ U` and `g : W ⟶ V`
there is a unique isomorphism `α_{g,f} : (f ∘ g)^* ≅ g^* ∘ f^*` of functors from the fibre over
`U` to the fibre over `W` such that, for every `y`, the chosen lift `(f ∘ g)^* y ⟶ y` is
`(α_{g,f})_y` followed by the chosen lifts `g^* f^* y ⟶ f^* y ⟶ y`. The compositor of
`c.pseudofunctor` satisfies this triangle (`pseudofunctor_mapComp_hom_app_fac`), so it is this
`α_{g,f}`. -/
@[stacks 02XO "(1), existence and uniqueness of the isomorphism, for an arbitrary choice of \
pullbacks"]
theorem existsUnique_compIso {W V U : 𝒮} (g : W ⟶ V) (f : V ⟶ U) :
    ∃! α : c.pullbackFunctor (g ≫ f) ≅ c.pullbackFunctor f ⋙ c.pullbackFunctor g,
      ∀ y : p.Fiber U, Fiber.fiberInclusion.map (α.hom.app y) ≫ c.map g (c.obj f y) ≫
        c.map f y = c.map (g ≫ f) y := by
  refine ⟨c.pullbackFunctorCompIso g f, fun y => c.objCompIso_hom_fac g f y, fun α hα => ?_⟩
  ext y
  exact congrArg Fiber.fiberInclusion.map <| fiber_hom_ext_of_cartesian (g ≫ f)
    (c.map g (c.obj f y) ≫ c.map f y) inferInstance (α.hom.app y)
    ((c.pullbackFunctorCompIso g f).hom.app y) ((hα y).trans (c.objCompIso_hom_fac g f y).symm)

end ChoiceOfPullbacks

/-! ### Categories fibred in groupoids -/

/-- In a category fibred in groupoids, a choice of morphisms `f^* x ⟶ x` lying over `f`, one for
every `f : V ⟶ U` and every `x` over `U`, is a choice of pullbacks: every morphism lying over `f`
is strongly cartesian over `f` (`IsFiberedInGroupoids.isStronglyCartesian_homLift`). -/
noncomputable def ChoiceOfPullbacks.ofIsFiberedInGroupoids {p : 𝒳 ⥤ 𝒮}
    (hp : p.IsFiberedInGroupoids) (obj : ∀ {V U : 𝒮} (_f : V ⟶ U), p.Fiber U → p.Fiber V)
    (map : ∀ {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U), (obj f x).1 ⟶ x.1)
    (isHomLift : ∀ {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U), p.IsHomLift f (map f x)) :
    p.ChoiceOfPullbacks where
  obj f x := obj f x
  map f x := map f x
  isStronglyCartesian f x :=
    have := isHomLift f x
    hp.isStronglyCartesian_homLift f (map f x)

/-- **Stacks 003V.** For a functor `p : 𝒳 ⥤ 𝒮`:

1. `p` is fibred in groupoids if and only if `p` is a fibred category and every fibre category
   `p.Fiber S` is a groupoid;
2. moreover, if `p` is fibred in groupoids then every morphism `φ` of `𝒳` is strongly cartesian
   (over `p.map φ`), and for every choice of morphisms `f^* x ⟶ x` lying over `f`, for all
   `f : V ⟶ U` and all `x` over `U`, the data `(U ↦ 𝒳_U, f ↦ f^*, α_{g,f}, α_U)` of Stacks 02XO
   form a pseudofunctor `𝒮ᵒᵖ ⥤ᵖ Cat` (`ChoiceOfPullbacks.pseudofunctor`) every value of which is a
   groupoid, i.e. a pseudofunctor into the `(2, 1)`-category of groupoids.

The pseudofunctor is that of `ChoiceOfPullbacks.ofIsFiberedInGroupoids`; its value at `f` is the
pullback functor `f^*` of the given lifts (`ChoiceOfPullbacks.pseudofunctor_map`), and its unitor
and compositor are characterised by `ChoiceOfPullbacks.pseudofunctor_mapId_hom_app`,
`ChoiceOfPullbacks.pseudofunctor_mapComp_hom_app_fac` and
`ChoiceOfPullbacks.pseudofunctor_mapComp_hom_app_unique`. -/
@[stacks 003V "the equivalence (1) ⇔ (2), every morphism strongly cartesian, and the \
groupoid-valued pseudofunctor of Lemma 02XO attached to any choice of lifts"]
theorem isFiberedInGroupoids_iff_and_isStronglyCartesian_and_isGroupoid (p : 𝒳 ⥤ 𝒮) :
    (p.IsFiberedInGroupoids ↔ p.IsFibered ∧ ∀ S, IsGroupoid (p.Fiber S)) ∧
      ∀ hp : p.IsFiberedInGroupoids,
        (∀ {x y : 𝒳} (φ : y ⟶ x), p.IsStronglyCartesian (p.map φ) φ) ∧
        ∀ (obj : ∀ {V U : 𝒮} (_f : V ⟶ U), p.Fiber U → p.Fiber V)
          (map : ∀ {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U), (obj f x).1 ⟶ x.1)
          (isHomLift : ∀ {V U : 𝒮} (f : V ⟶ U) (x : p.Fiber U), p.IsHomLift f (map f x))
          (U : LocallyDiscrete 𝒮ᵒᵖ),
          IsGroupoid
            ((ChoiceOfPullbacks.ofIsFiberedInGroupoids hp obj map isHomLift).pseudofunctor.obj U) :=
  ⟨IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid, fun hp =>
    ⟨fun φ => hp.isStronglyCartesian φ, fun _ _ _ U => hp.fiber_isGroupoid U.as.unop⟩⟩

end CategoryTheory.Functor
