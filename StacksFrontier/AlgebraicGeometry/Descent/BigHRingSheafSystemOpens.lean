module

public import StacksFrontier.AlgebraicGeometry.Descent.BigHRingSheafSystemUnit
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.BigHOverOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice

/-!
# Extension of scalars to an open, for a system of sheaves of rings

Let `𝓡` be a system of sheaves of rings on the big h category over `S`
(`AlgebraicGeometry.BigHOver.RingSheafSystem`). For an object `U` and an open `V` of its
underlying scheme, the open `V` is again an object of the site
(`AlgebraicGeometry.BigHOver.opensObj`) and its inclusion is an arrow
(`AlgebraicGeometry.BigHOver.opensι`).

The one property of `𝓡` that Zariski descent consumes is that **extension of scalars to an open
is restriction**, in the following form: the unit `M ⟶ ι_* ι^* M` of the adjunction between
extension of scalars and pushforward along the inclusion of `V` is bijective on the sections over
every open contained in `V` (`AlgebraicGeometry.BigHOver.RingSheafSystem.UnitBijective`). This
file derives from it everything else about inclusions of opens that the gluing needs: that the
counit is invertible, that the same holds for the inclusion of a smaller open into a larger one,
and that morphisms are detected on the opens contained in `V`.

## Main definitions

* `AlgebraicGeometry.BigHOver.RingSheafSystem.UnitBijective`: the restriction property of a
  system of sheaves of rings.

## Main results

* `AlgebraicGeometry.BigHOver.RingSheafSystem.isIso_of_bijective_push_app`: a morphism of
  modules on an open is invertible as soon as its pushforward is bijective on the sections over
  the opens contained in it.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.isIso_counit`: the counit along the inclusion of an
  open is invertible.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.bijective_unit_opensHom`: the unit along the
  inclusion of a smaller open into a larger one is bijective on the relevant sections.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.hom_ext_push`: morphisms into a pushforward from an
  open are determined on the opens contained in it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.BigHOver.RingSheafSystem

universe u

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (𝓡 : RingSheafSystem B S hS)

/-- **The restriction property of a system of sheaves of rings**: along the inclusion of every
open `V` of every object `U`, the unit of extension of scalars is bijective on the sections over
the opens contained in `V`. -/
def UnitBijective : Prop :=
  ∀ (U : BigHOver B S hS) (V : ((toScheme B S hS).obj U).Opens)
    (M : SheafOfModules.{u} (𝓡.ring U)) (T : ((toScheme B S hS).obj U).Opens), T ≤ V →
    Function.Bijective (((𝓡.adj (opensι B S hS V)).unit.app M).val.app (op T))

section Sections

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- An isomorphism of sheaves of modules is bijective on sections. -/
lemma bijective_app_of_isIso {P Q : SheafOfModules.{u} R} (g : P ⟶ Q) [IsIso g] (T : Cᵒᵖ) :
    Function.Bijective (g.val.app T) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨(inv g).val.app T, fun x => ?_, fun y => ?_⟩
  · change ((g ≫ inv g).val.app T) x = x
    rw [IsIso.hom_inv_id]
    rfl
  · change ((inv g ≫ g).val.app T) y = y
    rw [IsIso.inv_hom_id]
    rfl

/-- The restriction map of a presheaf of modules along an equality of objects is bijective. -/
lemma bijective_map_eqToHom (P : PresheafOfModules.{u} R.obj) {A A' : Cᵒᵖ} (h : A = A') :
    Function.Bijective (P.map (eqToHom h)) := by
  subst h
  rw [eqToHom_refl, PresheafOfModules.map_id]
  exact Function.bijective_id

/-- The restriction map of a presheaf of modules along a morphism between equal objects is
bijective. -/
lemma bijective_map_of_eq (P : PresheafOfModules.{u} R.obj) {A A' : Cᵒᵖ} (f : A ⟶ A')
    (h : A = A') [Quiver.IsThin C] : Function.Bijective (P.map f) := by
  subst h
  rw [Subsingleton.elim f (𝟙 _), PresheafOfModules.map_id]
  exact Function.bijective_id

/-- Sections of a composite of morphisms of sheaves of modules. -/
lemma coe_app_comp {P Q Q' : SheafOfModules.{u} R} (f : P ⟶ Q) (g : Q ⟶ Q') (T : Cᵒᵖ) :
    ⇑(ConcreteCategory.hom ((f ≫ g).val.app T)) =
      ⇑(ConcreteCategory.hom (g.val.app T)) ∘ ⇑(ConcreteCategory.hom (f.val.app T)) :=
  rfl

/-- Equal morphisms of sheaves of modules have equal sections maps, as functions. -/
lemma coe_app_congr {P Q : SheafOfModules.{u} R} {f g : P ⟶ Q} (h : f = g) (T : Cᵒᵖ) :
    ⇑(ConcreteCategory.hom (f.val.app T)) = ⇑(ConcreteCategory.hom (g.val.app T)) := by
  rw [h]

/-- Two morphisms agreeing on a pair of sections keep agreeing after postcomposition with a
common morphism. -/
lemma app_comp_eq_of_app_eq {A B Q Q' : SheafOfModules.{u} R} {f : A ⟶ Q} {g : B ⟶ Q}
    (r : Q ⟶ Q') {f' : A ⟶ Q'} {g' : B ⟶ Q'} (hf : f ≫ r = f') (hg : g ≫ r = g') {T : Cᵒᵖ}
    (s : ToType (A.val.obj T)) (t : ToType (B.val.obj T)) (h : g.val.app T t = f.val.app T s) :
    g'.val.app T t = f'.val.app T s := by
  subst hf hg
  exact congrArg (r.val.app T) h

/-- Sections of a composite of morphisms of sheaves of modules are bijective if both are. -/
private lemma bijective_app_comp {P Q Q' : SheafOfModules.{u} R} {f : P ⟶ Q} {g : Q ⟶ Q'}
    {T : Cᵒᵖ} (hf : Function.Bijective (f.val.app T)) (hg : Function.Bijective (g.val.app T)) :
    Function.Bijective ((f ≫ g).val.app T) :=
  hg.comp hf

/-- If a composite is bijective on sections and its first factor is, so is the second. -/
private lemma bijective_app_of_comp_left {P Q Q' : SheafOfModules.{u} R} {f : P ⟶ Q}
    {g : Q ⟶ Q'} {T : Cᵒᵖ} (hf : Function.Bijective (f.val.app T))
    (h : Function.Bijective ((f ≫ g).val.app T)) : Function.Bijective (g.val.app T) :=
  (Function.Bijective.of_comp_iff _ hf).mp h

/-- If a composite is bijective on sections and its second factor is, so is the first. -/
private lemma bijective_app_of_comp_right {P Q Q' : SheafOfModules.{u} R} {f : P ⟶ Q}
    {g : Q ⟶ Q'} {T : Cᵒᵖ} (hg : Function.Bijective (g.val.app T))
    (h : Function.Bijective ((f ≫ g).val.app T)) : Function.Bijective (f.val.app T) :=
  (Function.Bijective.of_comp_iff' hg _).mp h

end Sections

variable {U : BigHOver B S hS}

/-- Every open of the open subscheme `V` is the preimage of an open contained in `V`. -/
private lemma exists_le_preimage_eq {X : Scheme.{u}} (V : X.Opens) (T' : V.toScheme.Opens) :
    ∃ T : X.Opens, T ≤ V ∧ (Opens.map V.ι.base).obj T = T' :=
  ⟨V.ι ''ᵁ T', (V.ι.image_le_opensRange _).trans_eq V.opensRange_ι, V.ι.preimage_image_eq _⟩

/-- **A morphism of modules on an open is invertible as soon as its pushforward is bijective on
the sections over the opens contained in it.** Every open of the open subscheme `V` is the
preimage of an open contained in `V`. -/
lemma isIso_of_bijective_push_app {V : ((toScheme B S hS).obj U).Opens}
    {P Q : SheafOfModules.{u} (𝓡.ring (opensObj B S hS V))} (g : P ⟶ Q)
    (h : ∀ T : ((toScheme B S hS).obj U).Opens, T ≤ V →
      Function.Bijective (((𝓡.push (opensι B S hS V)).map g).val.app (op T))) :
    IsIso g := by
  refine Stacks.SheafOfModules.isIso_of_bijective_app g fun T' => ?_
  induction T' with | op T' => ?_
  obtain ⟨T, hT, hT'⟩ := exists_le_preimage_eq V T'
  subst hT'
  exact h T hT

/-- **Morphisms of modules on an open are determined by their pushforwards on the sections over
the opens contained in it.** -/
lemma hom_ext_of_push_app {V : ((toScheme B S hS).obj U).Opens}
    {P Q : SheafOfModules.{u} (𝓡.ring (opensObj B S hS V))} (g g' : P ⟶ Q)
    (h : ∀ T : ((toScheme B S hS).obj U).Opens, T ≤ V →
      ∀ x, ((𝓡.push (opensι B S hS V)).map g).val.app (op T) x =
        ((𝓡.push (opensι B S hS V)).map g').val.app (op T) x) :
    g = g' := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T' => ?_)
  induction T' with | op T' => ?_
  obtain ⟨T, hT, hT'⟩ := exists_le_preimage_eq V T'
  subst hT'
  exact ModuleCat.hom_ext (LinearMap.ext fun x => h T hT x)

/-- The restriction map of a pushforward from an open `W` from an open `V` to `V ⊓ W` is
bijective: both have the same preimage in `W`. -/
private lemma bijective_push_map_inf_aux {W : ((toScheme B S hS).obj U).Opens}
    (Q : SheafOfModules.{u} (𝓡.ring (opensObj B S hS W))) (V : ((toScheme B S hS).obj U).Opens) :
    Function.Bijective (((𝓡.push (opensι B S hS W)).obj Q).val.map
      (homOfLE (inf_le_left : V ⊓ W ≤ V)).op) := by
  have heq : (Opens.map W.ι.base).obj (V ⊓ W) = (Opens.map W.ι.base).obj V := by
    ext x
    simp only [SetLike.mem_coe]
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, x.2⟩⟩
  exact bijective_map_of_eq Q.val ((Opens.map W.ι.base).op.map
    (homOfLE (inf_le_left : V ⊓ W ≤ V)).op) (congrArg op heq.symm)

/-- **Morphisms into a pushforward from an open are determined on the opens contained in it.**
The sections of the pushforward over an open `T` and over `T ⊓ V` are the same, so the restriction
between them is injective. -/
lemma hom_ext_push {V : ((toScheme B S hS).obj U).Opens} {N : SheafOfModules.{u} (𝓡.ring U)}
    {Q : SheafOfModules.{u} (𝓡.ring (opensObj B S hS V))}
    (α β : N ⟶ (𝓡.push (opensι B S hS V)).obj Q)
    (h : ∀ T : ((toScheme B S hS).obj U).Opens, T ≤ V → α.val.app (op T) = β.val.app (op T)) :
    α = β := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => ?_)
  have hinj := (𝓡.bijective_push_map_inf_aux Q T.unop).1
  refine ModuleCat.hom_ext (LinearMap.ext fun x => hinj ?_)
  rw [← PresheafOfModules.naturality_apply, ← PresheafOfModules.naturality_apply]
  rw [h _ inf_le_right]

/-- The triangle comparison of pushforwards, on sections: a restriction along an equality of
opens. -/
lemma pushTriangle_hom_app_val_app {Y X U : BigHOver B S hS} (b : Y ⟶ X) (a : X ⟶ U)
    (q : Y ⟶ U) (h : b ≫ a = q) (Z : SheafOfModules.{u} (𝓡.ring Y))
    (T : (((toScheme B S hS).obj U).Opens))
    (x : ToType (((𝓡.push b ⋙ 𝓡.push a).obj Z).val.obj (op T))) :
    ((𝓡.pushTriangle b a q h).hom.app Z).val.app (op T) x =
      Z.val.map (eqToHom (by rw [← h]; rfl)).op x := by
  subst h
  exact (PresheafOfModules.map_id_apply _ _ _).symm


/-- Two composites of restriction maps of a presheaf of modules on a space between the same
opens agree. -/
lemma map_map_eq_map_map {X : TopCat.{u}} {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}}
    (P : PresheafOfModules.{u} R) {A A₁ A₂ A' : (Opens X)ᵒᵖ} (f₁ : A ⟶ A₁) (g₁ : A₁ ⟶ A')
    (f₂ : A ⟶ A₂) (g₂ : A₂ ⟶ A') (x : P.obj A) :
    P.map g₁ (P.map f₁ x) = P.map g₂ (P.map f₂ x) := by
  rw [← PresheafOfModules.map_comp_apply, ← PresheafOfModules.map_comp_apply,
    Subsingleton.elim (f₁ ≫ g₁) (f₂ ≫ g₂)]

/-- The restriction maps of a pushforward are restriction maps of the original module. -/
lemma push_obj_map_apply {Y U : BigHOver B S hS} (c : Y ⟶ U) (Z : SheafOfModules.{u} (𝓡.ring Y))
    {T T' : (((toScheme B S hS).obj U).Opens)ᵒᵖ} (g : T ⟶ T')
    (x : ToType (((𝓡.push c).obj Z).val.obj T)) :
    ((𝓡.push c).obj Z).val.map g x =
      Z.val.map ((Opens.map ((toScheme B S hS).map c).base).op.map g) x :=
  rfl

/-- **The triangle comparisons of pushforwards are associative.** -/
lemma pushTriangle_assoc {Y' Y X U : BigHOver B S hS} (c : Y' ⟶ Y) (b : Y ⟶ X) (a : X ⟶ U)
    (bc : Y' ⟶ X) (hbc : c ≫ b = bc) (q : Y ⟶ U) (hq : b ≫ a = q) (q' : Y' ⟶ U)
    (h1 : bc ≫ a = q') (h2 : c ≫ q = q') (Z : SheafOfModules.{u} (𝓡.ring Y')) :
    (𝓡.push a).map ((𝓡.pushTriangle c b bc hbc).hom.app Z) ≫
        (𝓡.pushTriangle bc a q' h1).hom.app Z =
      (𝓡.pushTriangle b a q hq).hom.app ((𝓡.push c).obj Z) ≫
        (𝓡.pushTriangle c q q' h2).hom.app Z := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun T => ?_)
  induction T with | op T => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  have l1 := 𝓡.pushTriangle_hom_app_val_app c b bc hbc Z
    ((Opens.map ((toScheme B S hS).map a).base).obj T) x
  have l2 := 𝓡.pushTriangle_hom_app_val_app bc a q' h1 Z T
    (((𝓡.pushTriangle c b bc hbc).hom.app Z).val.app _ x)
  have l3 := 𝓡.pushTriangle_hom_app_val_app b a q hq ((𝓡.push c).obj Z) T x
  have l4 := 𝓡.pushTriangle_hom_app_val_app c q q' h2 Z T
    (((𝓡.pushTriangle b a q hq).hom.app ((𝓡.push c).obj Z)).val.app (op T) x)
  refine l2.trans ((congrArg (Z.val.map _) l1).trans ?_)
  refine Eq.trans ?_ (l4.trans ((congrArg (Z.val.map _) l3).trans
    (congrArg (Z.val.map _) (𝓡.push_obj_map_apply c Z _ x)))).symm
  exact map_map_eq_map_map Z.val _ _ _ _ x

/-- The inclusions of nested opens compose. -/
@[reassoc (attr := simp)]
lemma opensHom_comp_opensHom {V W W' : ((toScheme B S hS).obj U).Opens} (h₁ : V ≤ W)
    (h₂ : W ≤ W') :
    opensHom B S hS h₁ ≫ opensHom B S hS h₂ = opensHom B S hS (h₁.trans h₂) :=
  Over.OverMorphism.ext (ObjectProperty.hom_ext _ (Scheme.homOfLE_homOfLE _ h₁ h₂))

/-- The restriction map of a pushforward from an open `W` from an open `V` to `V ⊓ W` is
bijective: both have the same preimage in `W`. -/
lemma bijective_push_map_inf {W : ((toScheme B S hS).obj U).Opens}
    (Q : SheafOfModules.{u} (𝓡.ring (opensObj B S hS W))) (V : ((toScheme B S hS).obj U).Opens) :
    Function.Bijective (((𝓡.push (opensι B S hS W)).obj Q).val.map
      (homOfLE (inf_le_left : V ⊓ W ≤ V)).op) :=
  𝓡.bijective_push_map_inf_aux Q V

/-- **The comparison of pushforwards of restrictions along a smaller object.** For
`c : Y' ⟶ Y` over `a : Y ⟶ X` and `q : Y ⟶ U`, the unit along `c` read through the triangle
comparisons. -/
def rhoG {Y Y' X U : BigHOver B S hS} (a : Y ⟶ X) (c : Y' ⟶ Y) (a' : Y' ⟶ X) (h : c ≫ a = a')
    (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : c ≫ q = q') (M : SheafOfModules.{u} (𝓡.ring X)) :
    (𝓡.push q).obj ((𝓡.pull a.op).obj M) ⟶ (𝓡.push q').obj ((𝓡.pull a'.op).obj M) :=
  (𝓡.push q).map ((𝓡.adj c).unit.app ((𝓡.pull a.op).obj M)) ≫
    (𝓡.pushTriangle c q q' hq).hom.app ((𝓡.pull c.op).obj ((𝓡.pull a.op).obj M)) ≫
    (𝓡.push q').map (𝓡.compInv a c a' h M)

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.rhoG` intertwines a morphism with its transport
along `c`. -/
lemma push_map_rhoG {Y Y' X₁ X₂ U : BigHOver B S hS} (a₁ : Y ⟶ X₁) (a₂ : Y ⟶ X₂) (c : Y' ⟶ Y)
    (a₁' : Y' ⟶ X₁) (a₂' : Y' ⟶ X₂) (h₁ : c ≫ a₁ = a₁') (h₂ : c ≫ a₂ = a₂')
    (q : Y ⟶ U) (q' : Y' ⟶ U) (hq : c ≫ q = q') {M₁ : SheafOfModules.{u} (𝓡.ring X₁)}
    {M₂ : SheafOfModules.{u} (𝓡.ring X₂)} (φ : (𝓡.pull a₁.op).obj M₁ ⟶ (𝓡.pull a₂.op).obj M₂) :
    (𝓡.push q).map φ ≫ 𝓡.rhoG a₂ c a₂' h₂ q q' hq M₂ =
      𝓡.rhoG a₁ c a₁' h₁ q q' hq M₁ ≫ (𝓡.push q').map
        (𝓡.compHom a₁ c a₁' h₁ M₁ ≫ (𝓡.pull c.op).map φ ≫ 𝓡.compInv a₂ c a₂' h₂ M₂) := by
  simp only [rhoG, Category.assoc]
  rw [← Functor.map_comp (𝓡.push q') (𝓡.compInv _ _ _ _ _), compInv_compHom_assoc,
    Functor.map_comp]
  have nat2 := (𝓡.pushTriangle c q q' hq).hom.naturality ((𝓡.pull c.op).map φ)
  simp only [Functor.comp_map] at nat2
  rw [← reassoc_of% nat2]
  have nat1 := (𝓡.adj c).unit.naturality φ
  simp only [Functor.comp_map, Functor.id_map] at nat1
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, nat1]

/-- **The unit along `a`, read through the triangle comparison**: for `a ≫ g = q`, the comparison
of the pushforward along `g` of a module with the pushforward along `q` of its restriction. -/
def etaG {Y X U : BigHOver B S hS} (a : Y ⟶ X) (g : X ⟶ U) (q : Y ⟶ U) (h : a ≫ g = q)
    (M : SheafOfModules.{u} (𝓡.ring X)) :
    (𝓡.push g).obj M ⟶ (𝓡.push q).obj ((𝓡.pull a.op).obj M) :=
  (𝓡.push g).map ((𝓡.adj a).unit.app M) ≫
    (𝓡.pushTriangle a g q h).hom.app ((𝓡.pull a.op).obj M)

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.etaG` followed by a morphism. -/
lemma etaG_comp_push_map {Y X U : BigHOver B S hS} (a : Y ⟶ X) (g : X ⟶ U) (q : Y ⟶ U)
    (h : a ≫ g = q) (M : SheafOfModules.{u} (𝓡.ring X)) {Z : SheafOfModules.{u} (𝓡.ring Y)}
    (k : (𝓡.pull a.op).obj M ⟶ Z) :
    𝓡.etaG a g q h M ≫ (𝓡.push q).map k =
      (𝓡.push g).map ((𝓡.adj a).homEquiv M Z k) ≫ (𝓡.pushTriangle a g q h).hom.app Z := by
  have nat := (𝓡.pushTriangle a g q h).hom.naturality k
  simp only [Functor.comp_map] at nat
  rw [etaG, Category.assoc, ← nat, Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]

/-- **The comparison of a pushforward with a smaller object factors through a larger one.** -/
lemma etaG_comp_rhoG {Y Y' X U : BigHOver B S hS} (a : Y ⟶ X) (c : Y' ⟶ Y) (a' : Y' ⟶ X)
    (hc : c ≫ a = a') (g : X ⟶ U) (q : Y ⟶ U) (q' : Y' ⟶ U) (h : a ≫ g = q) (h' : a' ≫ g = q')
    (hq : c ≫ q = q') (M : SheafOfModules.{u} (𝓡.ring X)) :
    𝓡.etaG a g q h M ≫ 𝓡.rhoG a c a' hc q q' hq M = 𝓡.etaG a' g q' h' M := by
  have hu := 𝓡.unit_comp_push_map_mapComp'_hom a c a' hc M
  have hu' : (𝓡.adj a').unit.app M =
      ((𝓡.adj a).unit.app M ≫ (𝓡.push a).map ((𝓡.adj c).unit.app ((𝓡.pull a.op).obj M)) ≫
        (𝓡.pushTriangle c a a' hc).hom.app _) ≫ (𝓡.push a').map (𝓡.compInv a c a' hc M) := by
    rw [← hu, Category.assoc, ← Functor.map_comp, compHom_compInv, CategoryTheory.Functor.map_id]
    exact (Category.comp_id _).symm
  simp only [etaG, rhoG, hu', Functor.map_comp, Category.assoc]
  have nat1 := (𝓡.pushTriangle a' g q' h').hom.naturality (𝓡.compInv a c a' hc M)
  simp only [Functor.comp_map] at nat1
  rw [nat1]
  have as := 𝓡.pushTriangle_assoc c a g a' hc q h q' h' hq
    ((𝓡.pull c.op).obj ((𝓡.pull a.op).obj M))
  rw [reassoc_of% as]
  have nat2 := (𝓡.pushTriangle a g q h).hom.naturality
    ((𝓡.adj c).unit.app ((𝓡.pull a.op).obj M))
  simp only [Functor.comp_map] at nat2
  rw [reassoc_of% nat2]

/-- The composition comparison `AlgebraicGeometry.BigHOver.RingSheafSystem.compHom` at a
commuting triangle `b ≫ a = q` is an isomorphism, with inverse
`AlgebraicGeometry.BigHOver.RingSheafSystem.compInv`. -/
instance isIso_compHom {Y X U : BigHOver B S hS} (a : X ⟶ U) (b : Y ⟶ X) (q : Y ⟶ U)
    (hq : b ≫ a = q) (M : SheafOfModules.{u} (𝓡.ring U)) : IsIso (𝓡.compHom a b q hq M) :=
  ⟨⟨_, 𝓡.compHom_compInv a b q hq M, 𝓡.compInv_compHom a b q hq M⟩⟩

variable {𝓡}

/-- **The counit along the inclusion of an open is invertible**, for a system with the
restriction property: by the triangle identity its pushforward is inverse to the unit over the
opens contained in the open. -/
lemma isIso_counit (h𝓡 : 𝓡.UnitBijective) {V : ((toScheme B S hS).obj U).Opens}
    (M : SheafOfModules.{u} (𝓡.ring (opensObj B S hS V))) :
    IsIso ((𝓡.adj (opensι B S hS V)).counit.app M) := by
  refine 𝓡.isIso_of_bijective_push_app _ fun T hT => ?_
  refine bijective_app_of_comp_left (h𝓡 U V ((𝓡.push (opensι B S hS V)).obj M) T hT) ?_
  rw [(𝓡.adj (opensι B S hS V)).right_triangle_components M]
  exact bijective_app_of_isIso _ _

/-- **The unit along the inclusion of a smaller open into a larger one is bijective** on the
sections over the preimages of the opens contained in the smaller one, for a system with the
restriction property. This follows from the same statement for the two inclusions into the
ambient object, through the unit along the triangle they form, and the invertibility of the
counit. -/
lemma bijective_unit_opensHom (h𝓡 : 𝓡.UnitBijective) {V W : ((toScheme B S hS).obj U).Opens}
    (h : V ≤ W) (M : SheafOfModules.{u} (𝓡.ring (opensObj B S hS W)))
    (T : ((toScheme B S hS).obj U).Opens) (hT : T ≤ V) :
    Function.Bijective (((𝓡.push (opensι B S hS W)).map
      ((𝓡.adj (opensHom B S hS h)).unit.app M)).val.app (op T)) := by
  set N := (𝓡.push (opensι B S hS W)).obj M
  have uc := 𝓡.unit_comp_push_map_mapComp'_hom (opensι B S hS W) (opensHom B S hS h)
    (opensι B S hS V) (opensHom_opensι B S hS h) N
  have h1 := bijective_app_of_comp_left (h𝓡 U W N T (hT.trans h)) (by
    rw [← uc]
    exact bijective_app_comp (h𝓡 U V N T hT) (bijective_app_of_isIso _ _))
  have h1' := bijective_app_of_comp_right (bijective_app_of_isIso _ _) h1
  have := isIso_counit h𝓡 M
  have nat := congrArg (𝓡.push (opensι B S hS W)).map
    ((𝓡.adj (opensHom B S hS h)).unit.naturality ((𝓡.adj (opensι B S hS W)).counit.app M))
  simp only [Functor.map_comp, Functor.id_obj, Functor.id_map] at nat
  refine bijective_app_of_comp_left (bijective_app_of_isIso
    ((𝓡.push (opensι B S hS W)).map ((𝓡.adj (opensι B S hS W)).counit.app M)) (op T)) ?_
  rw [nat]
  exact bijective_app_comp h1' (bijective_app_of_isIso _ _)

/-- `AlgebraicGeometry.BigHOver.RingSheafSystem.etaG` along the inclusion of a smaller open is
bijective on the sections over the opens contained in the smaller open, for a system with the
restriction property. -/
lemma bijective_etaG_opensHom (h𝓡 : 𝓡.UnitBijective) {P W : ((toScheme B S hS).obj U).Opens}
    (hP : P ≤ W) (M : SheafOfModules.{u} (𝓡.ring (opensObj B S hS W)))
    (V : ((toScheme B S hS).obj U).Opens) (hV : V ≤ P) :
    Function.Bijective ((𝓡.etaG (opensHom B S hS hP) (opensι B S hS W) (opensι B S hS P)
      (opensHom_opensι B S hS hP) M).val.app (op V)) := by
  rw [etaG, coe_app_comp]
  exact (bijective_app_of_isIso _ _).comp (bijective_unit_opensHom h𝓡 hP M V hV)

end AlgebraicGeometry.BigHOver.RingSheafSystem

end
