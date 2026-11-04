module

public import StacksFrontier.AlgebraicGeometry.RelativeCech.BaseChangePresheaf
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange

/-!
# Base change of the relative Čech complex
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.RelativeCechBaseChange

open Stacks.AlgebraicGeometry.RelativeCech

variable {W Y X X' S : Scheme.{u}}

/-- A transport along an equality of an object with itself is the identity. -/
theorem comp_eqToHom_refl {C : Type*} [Category* C] {A B : C} (f : B ⟶ A) (h : A = A) :
    f ≫ eqToHom h = f := by
  simp

/-- The components of `relativeUnit'`: `relativeUnit` followed by the transport along the
factorisation. -/
theorem relativeUnit'_app (u : W ⟶ Y) (b : Y ⟶ X) (a : W ⟶ X) (h : u ≫ b = a)
    (M : X.Modules) :
    (relativeUnit' u b a h).app M = (relativeUnit u b).app M ≫
      eqToHom (congrArg (fun m : W ⟶ X ↦ (pushforward m).obj ((pullback m).obj M)) h) := by
  subst h
  simp only [relativeUnit', NatTrans.comp_app, eqToHom_app]

/-- Transport of a pushforward along an equality of morphisms. -/
theorem eqToHom_comp_pushforward_map {p q : W ⟶ X} (hpq : p = q) (M : X.Modules)
    {N : W.Modules} (x : (pullback q).obj M ⟶ N) :
    eqToHom (congrArg (fun m : W ⟶ X ↦ (pushforward m).obj ((pullback m).obj M)) hpq) ≫
        (pushforward q).map x =
      (pushforward p).map
          (eqToHom (congrArg (fun m : W ⟶ X ↦ (pullback m).obj M) hpq) ≫ x) ≫
        eqToHom (congrArg (fun m : W ⟶ X ↦ (pushforward m).obj N) hpq) := by
  subst hpq
  simp

/-- `eqToHom_comp_pushforward_map` at the two bracketings of a triple composite. -/
theorem eqToHom_comp_pushforward_map_assoc (u : W ⟶ Y) (b : Y ⟶ X') (k : X' ⟶ X)
    (M : X.Modules) :
    eqToHom (congrArg (fun m : W ⟶ X ↦ (pushforward m).obj ((Scheme.Modules.pullback m).obj M))
        (Category.assoc u b k).symm) ≫
        (pushforward ((u ≫ b) ≫ k)).map ((pullbackComp (u ≫ b) k).inv.app M) =
      (pushforward (u ≫ b ≫ k)).map
        (eqToHom (congrArg (fun m : W ⟶ X ↦ (Scheme.Modules.pullback m).obj M)
          (Category.assoc u b k).symm) ≫ (pullbackComp (u ≫ b) k).inv.app M) :=
  (eqToHom_comp_pushforward_map (Category.assoc u b k).symm M _).trans
    (comp_eqToHom_refl _ _)

/-- The restriction map over `X'`, pushed forward along `k`, written through the transpose. -/
theorem relativeUnit_tail (u : W ⟶ Y) (b : Y ⟶ X') (k : X' ⟶ X) (M : X.Modules) :
    (pushforward (b ≫ k)).map ((pullbackComp b k).inv.app M ≫
        (pullbackPushforwardAdjunction u).homEquiv _ _
          ((pullbackComp u b).hom.app ((Scheme.Modules.pullback k).obj M))) =
      (pushforward (b ≫ k)).map ((pullbackComp b k).inv.app M) ≫
        (pushforward k).map ((relativeUnit u b).app ((Scheme.Modules.pullback k).obj M)) := by
  rw [relativeUnit_app']
  exact Functor.map_comp _ _ _

/-- The naturality square of `relativeMonadMapIso`, with the factorisation `u ≫ b = c` as a
variable. -/
theorem relativeUnit'_comp_pullbackComp_inv (u : W ⟶ Y) (b : Y ⟶ X') (c : W ⟶ X')
    (h : u ≫ b = c) (k : X' ⟶ X) (h' : u ≫ b ≫ k = c ≫ k) (M : X.Modules) :
    (relativeUnit' u (b ≫ k) (c ≫ k) h').app M ≫
        (pushforward (c ≫ k)).map ((pullbackComp c k).inv.app M) =
      (pushforward (b ≫ k)).map ((pullbackComp b k).inv.app M) ≫
        (pushforward k).map ((relativeUnit' u b c h).app ((Scheme.Modules.pullback k).obj M)) := by
  subst h
  rw [relativeUnit'_app, relativeUnit'_app, eqToHom_refl, Category.comp_id]
  refine (Category.assoc _ _ _).trans ?_
  rw [eqToHom_comp_pushforward_map_assoc u b k M]
  refine (relativeUnit_comp_pullbackComp u b k M rfl).trans ?_
  exact relativeUnit_tail u b k M

/-- The restriction maps of the presheaf of monads restricted along `Over.map k`. -/
theorem map_op_comp_flip_map (k : X' ⟶ X) (M : X.Modules) {B C : (Over X')ᵒᵖ} (φ : B ⟶ C) :
    ((Over.map k).op ⋙ (relativeMonad X).flip.obj M).map φ =
      (relativeUnit' ((Over.map k).map φ.unop).left ((Over.map k).obj B.unop).hom
        ((Over.map k).obj C.unop).hom (Over.w ((Over.map k).map φ.unop))).app M := by
  rw [Functor.comp_map, Functor.op_map, Functor.flip_obj_map]
  exact congrArg (fun t ↦ NatTrans.app t M) (relativeMonad_map X ((Over.map k).map φ.unop))

/-- The restriction maps of the presheaf of monads followed by a pushforward. -/
theorem flip_comp_pushforward_map (k : X' ⟶ X) (N : X'.Modules) {B C : (Over X')ᵒᵖ}
    (φ : B ⟶ C) :
    ((relativeMonad X').flip.obj N ⋙ pushforward k).map φ =
      (pushforward k).map ((relativeUnit' φ.unop.left B.unop.hom C.unop.hom
        (Over.w φ.unop)).app N) := by
  rw [Functor.comp_map, Functor.flip_obj_map]
  exact congrArg (fun t ↦ (pushforward k).map (NatTrans.app t N)) (relativeMonad_map X' φ.unop)

/-- The restriction map of the presheaf of monads at the image of a morphism under `Over.map k`
is the restriction map along the same morphism of schemes. -/
theorem relativeUnit'_overMap (k : X' ⟶ X) {B C : Over X'} (ψ : C ⟶ B) :
    relativeUnit' ((Over.map k).map ψ).left ((Over.map k).obj B).hom ((Over.map k).obj C).hom
      (Over.w ((Over.map k).map ψ)) =
    relativeUnit' ψ.left (B.hom ≫ k) (C.hom ≫ k) (by rw [← Category.assoc, Over.w ψ]) := rfl

/-- `relativeUnit'_overMap`, componentwise. -/
theorem relativeUnit'_overMap_app (k : X' ⟶ X) (M : X.Modules) {B C : Over X'} (ψ : C ⟶ B) :
    (relativeUnit' ((Over.map k).map ψ).left ((Over.map k).obj B).hom ((Over.map k).obj C).hom
      (Over.w ((Over.map k).map ψ))).app M =
    (relativeUnit' ψ.left (B.hom ≫ k) (C.hom ≫ k) (by rw [← Category.assoc, Over.w ψ])).app M :=
  congrArg (fun t ↦ NatTrans.app t M) (relativeUnit'_overMap k ψ)

/-- The naturality square of `relativeMonadMapIso`. -/
theorem relativeMonadMapIso_naturality (k : X' ⟶ X) (M : X.Modules) {B C : (Over X')ᵒᵖ}
    (φ : B ⟶ C) :
    ((Over.map k).op ⋙ (relativeMonad X).flip.obj M).map φ ≫
        (pushforward (C.unop.hom ≫ k)).map ((pullbackComp C.unop.hom k).inv.app M) =
      (pushforward (B.unop.hom ≫ k)).map ((pullbackComp B.unop.hom k).inv.app M) ≫
        ((relativeMonad X').flip.obj ((Scheme.Modules.pullback k).obj M) ⋙ pushforward k).map φ :=
  by
  rw [map_op_comp_flip_map, relativeUnit'_overMap_app, flip_comp_pushforward_map]
  exact relativeUnit'_comp_pullbackComp_inv φ.unop.left B.unop.hom C.unop.hom (Over.w φ.unop) k _ M

/-- **The presheaf of monads restricted along `Over.map k`.**  For `k : X' ⟶ X` and an
`𝒪_X`-module `M`, the presheaf `B ↦ (b ≫ k)_* (b ≫ k)^* M` on `Over X'` is the presheaf
`B ↦ k_* b_* b^* k^* M`, through the comparison `(b ≫ k)^* ≅ b^* k^*`. -/
noncomputable def relativeMonadMapIso (k : X' ⟶ X) (M : X.Modules) :
    (Over.map k).op ⋙ (relativeMonad X).flip.obj M ≅
      (relativeMonad X').flip.obj ((Scheme.Modules.pullback k).obj M) ⋙ pushforward k :=
  NatIso.ofComponents
    (fun B ↦ (pushforward (B.unop.hom ≫ k)).mapIso ((pullbackComp B.unop.hom k).symm.app M))
    (fun {_ _} φ ↦ relativeMonadMapIso_naturality k M φ)

/-! ### The base change comparison of the coefficient presheaves -/

section BaseChange

variable {S S' : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

open Stacks.AlgebraicGeometry.AffinePushforward

/-- The coefficient presheaf `B ↦ ((b ≫ g') ≫ f)_* (b ≫ g')^* M` on `Over X'` is the direct image
along `g` of the coefficient presheaf `B ↦ (b ≫ f')_* b^* (g')^* M` of `f'`. -/
noncomputable def coefficientMapIso (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (Over.map g').op ⋙ ((relativeMonad X).flip.obj M ⋙ pushforward f) ≅
      ((relativeMonad X').flip.obj ((Scheme.Modules.pullback g').obj M) ⋙ pushforward f') ⋙
        pushforward g :=
  Functor.isoWhiskerRight (relativeMonadMapIso g' M) (pushforward f) ≪≫
    Functor.isoWhiskerLeft ((relativeMonad X').flip.obj ((Scheme.Modules.pullback g').obj M))
      (pushforwardSquareIso w)

/-- The naturality of `ε : G ⋙ Over.map g' ⟶ 𝟭`, read in `(Over X)ᵒᵖ`. -/
theorem counit_op_comp (g' : X' ⟶ X) {G : Over X ⥤ Over X'} (ε : G ⋙ Over.map g' ⟶ 𝟭 _)
    {A B : (Over X)ᵒᵖ} (φ : A ⟶ B) :
    φ ≫ (ε.app B.unop).op = (ε.app A.unop).op ≫ ((Over.map g').map (G.map φ.unop)).op :=
  Quiver.Hom.unop_inj (ε.naturality φ.unop).symm

/-- The maps of a presheaf restricted along `(Over.map g').op`. -/
theorem overMap_op_comp_map {C : Type*} [Category* C] (g' : X' ⟶ X) (P : (Over X)ᵒᵖ ⥤ C)
    {B B' : Over X'} (ψ : B ⟶ B') :
    ((Over.map g').op ⋙ P).map ψ.op = P.map ((Over.map g').map ψ).op := by
  rw [Functor.comp_map, Functor.op_map, Quiver.Hom.unop_op]

/-- The maps of a presheaf restricted along `G.op`. -/
theorem op_comp_map {C : Type*} [Category* C] (G : Over X ⥤ Over X') (R : (Over X')ᵒᵖ ⥤ C)
    {A B : (Over X)ᵒᵖ} (φ : A ⟶ B) :
    (G.op ⋙ R).map φ = R.map (G.map φ.unop).op := by
  rw [Functor.comp_map, Functor.op_map]

/-- The naturality of `restrictCounit`. -/
theorem restrictCounit_naturality {C : Type*} [Category* C] (g' : X' ⟶ X)
    {G : Over X ⥤ Over X'} (ε : G ⋙ Over.map g' ⟶ 𝟭 _)
    (P : (Over X)ᵒᵖ ⥤ C) (R : (Over X')ᵒᵖ ⥤ C) (θ : (Over.map g').op ⋙ P ⟶ R)
    {A B : (Over X)ᵒᵖ} (φ : A ⟶ B) :
    P.map φ ≫ (P.map (ε.app B.unop).op ≫ θ.app (op (G.obj B.unop))) =
      (P.map (ε.app A.unop).op ≫ θ.app (op (G.obj A.unop))) ≫ (G.op ⋙ R).map φ := by
  rw [← Category.assoc, ← Functor.map_comp, counit_op_comp, Functor.map_comp, Category.assoc,
    ← overMap_op_comp_map, θ.naturality, op_comp_map, Category.assoc]

/-- For a functor `G : Over X ⥤ Over X'` with `ε : G ⋙ Over.map g' ⟶ 𝟭`, a morphism
`(Over.map g').op ⋙ P ⟶ R` of presheaves on `Over X'` induces a morphism `P ⟶ G.op ⋙ R` of
presheaves on `Over X`, by restricting along `ε`. -/
@[simps]
noncomputable def restrictCounit {C : Type*} [Category* C] (g' : X' ⟶ X)
    {G : Over X ⥤ Over X'} (ε : G ⋙ Over.map g' ⟶ 𝟭 _)
    (P : (Over X)ᵒᵖ ⥤ C) (R : (Over X')ᵒᵖ ⥤ C) (θ : (Over.map g').op ⋙ P ⟶ R) :
    P ⟶ G.op ⋙ R where
  app A := P.map (ε.app A.unop).op ≫ θ.app (op (G.obj A.unop))
  naturality {_ _} φ := restrictCounit_naturality g' ε P R θ φ

/-- The transpose of a morphism `P ⟶ Q ⋙ G` of functors under an adjunction `L ⊣ G`. -/
@[simps]
def transposeNatTrans {J C D : Type*} [Category* J] [Category* C] [Category* D] {L : C ⥤ D}
    {G : D ⥤ C} (adj : L ⊣ G) {P : J ⥤ C} {Q : J ⥤ D} (γ : P ⟶ Q ⋙ G) : P ⋙ L ⟶ Q where
  app j := (adj.homEquiv _ _).symm (γ.app j)
  naturality {j j'} φ := by
    rw [Functor.comp_map, ← adj.homEquiv_naturality_left_symm, γ.naturality, Functor.comp_map,
      adj.homEquiv_naturality_right_symm]

/-- The comparison `(a ≫ f)_* a^* M ⟶ g_* (a' ≫ f')_* a'^* (g')^* M` of coefficient presheaves on
`Over X`, where `a' : G(A) ⟶ X'` is the structure morphism of `G(A)`: restriction along
`ε_A : G(A) ⟶ A`, followed by `coefficientMapIso`. -/
noncomputable def coefficientBaseChange (w : g' ≫ f = f' ≫ g) {G : Over X ⥤ Over X'}
    (ε : G ⋙ Over.map g' ⟶ 𝟭 _) (M : X.Modules) :
    (relativeMonad X).flip.obj M ⋙ pushforward f ⟶
      G.op ⋙
        (((relativeMonad X').flip.obj ((Scheme.Modules.pullback g').obj M) ⋙ pushforward f') ⋙
          pushforward g) :=
  restrictCounit g' ε _ _ (coefficientMapIso w M).hom

/-- **The base change map of coefficient presheaves**
`g^*((a ≫ f)_* a^* M) ⟶ (a' ≫ f')_* a'^* (g')^* M`, natural in `A : Over X`: the transpose of
`coefficientBaseChange` under `g^* ⊣ g_*`. -/
noncomputable def coefficientPullback (w : g' ≫ f = f' ≫ g) {G : Over X ⥤ Over X'}
    (ε : G ⋙ Over.map g' ⟶ 𝟭 _) (M : X.Modules) :
    ((relativeMonad X).flip.obj M ⋙ pushforward f) ⋙ Scheme.Modules.pullback g ⟶
      G.op ⋙
        ((relativeMonad X').flip.obj ((Scheme.Modules.pullback g').obj M) ⋙ pushforward f') :=
  transposeNatTrans (pullbackPushforwardAdjunction g) (coefficientBaseChange w ε M)

end BaseChange

section Identify

variable {A A' S : Scheme.{u}}

/-- For equal morphisms `p = q`, the transport `eqToHom` between pushforwards commutes with
pushing forward a morphism of modules. -/
theorem eqToHom_comp_pushforward_map' {p q : A' ⟶ S} (hpq : p = q) {Z Z' : A'.Modules}
    (x : Z ⟶ Z') :
    eqToHom (congrArg (fun m : A' ⟶ S ↦ (pushforward m).obj Z) hpq) ≫ (pushforward q).map x =
      (pushforward p).map x ≫ eqToHom (congrArg (fun m : A' ⟶ S ↦ (pushforward m).obj Z') hpq) := by
  subst hpq
  simp

/-- Pushing forward along `f` the composite of the unit of `h^* ⊣ h_*`, the comparison
`(h ≫ a)^* ≅ h^* a^*` and `ψ` is the corresponding composite of pushforwards along `a ≫ f` and
`h ≫ a ≫ f`. -/
theorem restriction_tail (h : A' ⟶ A) (a : A ⟶ X) (f : X ⟶ S) (M : X.Modules)
    (Q : A'.Modules) (ψ : (Scheme.Modules.pullback (h ≫ a)).obj M ⟶ Q) :
    (pushforward f).map ((pushforward a).map
        ((pullbackPushforwardAdjunction h).unit.app ((Scheme.Modules.pullback a).obj M) ≫
          (pushforward h).map ((pullbackComp h a).hom.app M))) ≫
        (pushforward f).map ((pushforward (h ≫ a)).map ψ) =
      (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward (h ≫ a ≫ f)).map ((pullbackComp h a).hom.app M ≫ ψ) := by
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- The components of the inverse of `pushforwardComp u b` are identities. -/
theorem pushforwardComp_inv_app {Y Z : Scheme.{u}} (u : Y ⟶ Z) (b : Z ⟶ S) (M : Y.Modules) :
    (pushforwardComp u b).inv.app M = 𝟙 _ := rfl

/-- `relativeUnit' h a (h ≫ a) rfl` agrees componentwise with `relativeUnit h a`. -/
theorem relativeUnit'_app_rfl (h : A' ⟶ A) (a : A ⟶ X) (M : X.Modules) :
    (relativeUnit' h a (h ≫ a) rfl).app M = (relativeUnit h a).app M := by
  rw [relativeUnit'_app, eqToHom_refl, Category.comp_id]

/-- Composing with the component of `pushforwardCongr rfl` does nothing. -/
theorem comp_pushforwardCongr_refl (p : A' ⟶ S) (Q : A'.Modules) {Z : S.Modules}
    (x : Z ⟶ (pushforward p).obj Q) :
    x ≫ (pushforwardCongr (rfl : p = p)).hom.app Q = x := by
  rw [pushforwardCongr_refl, Category.comp_id]

/-- Precomposing with the component of `pullbackCongr rfl` does nothing. -/
theorem pullbackCongr_refl_comp (p : A' ⟶ X) (M : X.Modules) {Q : A'.Modules}
    (x : (Scheme.Modules.pullback p).obj M ⟶ Q) :
    (pullbackCongr (rfl : p = p)).hom.app M ≫ x = x := by
  rw [pullbackCongr_refl, Category.id_comp]

/-- The composite of pushforwards along `a ≫ f` and `h ≫ a ≫ f` may be rewritten through
`pushforwardCongr hm₂` and the trivial `pullbackCongr rfl`, landing in the pushforward along
`(h ≫ a) ≫ f`. -/
theorem restriction_rhs (h : A' ⟶ A) (a : A ⟶ X) (f : X ⟶ S) (M : X.Modules) (Q : A'.Modules)
    (ψ : (Scheme.Modules.pullback (h ≫ a)).obj M ⟶ Q) (hm₂ : h ≫ a ≫ f = (h ≫ a) ≫ f) :
    (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward (h ≫ a ≫ f)).map ((pullbackComp h a).hom.app M ≫ ψ) =
      (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforwardCongr hm₂).hom.app
          ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward ((h ≫ a) ≫ f)).map ((pullbackComp h a).hom.app M ≫
          (pullbackCongr (rfl : h ≫ a = h ≫ a)).hom.app M ≫ ψ) := by
  rw [pullbackCongr_refl_comp, pushforwardCongr_hom_app_eqToHom hm₂
    ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback a).obj M)) rfl]
  exact congrArg (fun t ↦ _ ≫ t)
    ((eqToHom_comp_pushforward_map' hm₂ ((pullbackComp h a).hom.app M ≫ ψ)).trans
      (comp_eqToHom_refl _ (congrArg (fun m : A' ⟶ S ↦ (pushforward m).obj Q) hm₂))).symm

/-- Pushing forward along `f` the composite of `relativeUnit' h a (h ≫ a) rfl` and
`(h ≫ a)_* ψ` equals the composite of the unit of `h^* ⊣ h_*` pushed forward along `a ≫ f` with
the pushforward along `h ≫ a ≫ f` of `(pullbackComp h a).hom ≫ ψ`. -/
theorem restriction_lhs (h : A' ⟶ A) (a : A ⟶ X) (f : X ⟶ S) (M : X.Modules) (Q : A'.Modules)
    (ψ : (Scheme.Modules.pullback (h ≫ a)).obj M ⟶ Q) :
    (pushforward f).map ((relativeUnit' h a (h ≫ a) rfl).app M) ≫
        (pushforward f).map ((pushforward (h ≫ a)).map ψ) ≫
          (pushforwardCongr (rfl : (h ≫ a) ≫ f = (h ≫ a) ≫ f)).hom.app Q =
      (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward (h ≫ a ≫ f)).map ((pullbackComp h a).hom.app M ≫ ψ) := by
  refine (congrArg (fun t ↦ (pushforward f).map t ≫ _) (relativeUnit'_app_rfl h a M)).trans ?_
  refine (congrArg (fun t ↦ _ ≫ t) (comp_pushforwardCongr_refl _ _ _)).trans ?_
  refine (congrArg (fun t ↦ (pushforward f).map t ≫ _) (relativeUnit_app h a M)).trans ?_
  exact restriction_tail h a f M Q ψ

/-- For `h ≫ a = k` and `k ≫ f = m`, pushing forward along `f` the composite of
`relativeUnit' h a k hk` and `k_* ψ`, followed by `pushforwardCongr hm`, equals the unit of
`h^* ⊣ h_*` pushed forward along `a ≫ f`, followed by `pushforwardCongr hm₂` and the pushforward
along `m` of `(pullbackComp h a).hom ≫ (pullbackCongr hk).hom ≫ ψ`. -/
theorem restriction_comp_transport (h : A' ⟶ A) (a : A ⟶ X) (k : A' ⟶ X) (hk : h ≫ a = k)
    (f : X ⟶ S) (m : A' ⟶ S) (hm : k ≫ f = m) (hm₂ : h ≫ a ≫ f = m) (M : X.Modules)
    (Q : A'.Modules) (ψ : (Scheme.Modules.pullback k).obj M ⟶ Q) :
    (pushforward f).map ((relativeUnit' h a k hk).app M) ≫
        (pushforward f).map ((pushforward k).map ψ) ≫ (pushforwardCongr hm).hom.app Q =
      (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforwardCongr hm₂).hom.app
          ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward m).map ((pullbackComp h a).hom.app M ≫ (pullbackCongr hk).hom.app M ≫ ψ) := by
  subst hk hm
  exact (restriction_lhs h a f M Q ψ).trans (restriction_rhs h a f M Q ψ hm₂)

variable {X' S' : Scheme.{u}}

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- The component at a pushforward of the comparison of the composite direct images around a
commutative square. -/
theorem pushforwardSquareIso_app_pushforward {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) (a' : A' ⟶ X') (Q : A'.Modules)
    (hm : (a' ≫ g') ≫ f = (a' ≫ f') ≫ g) :
    (pushforwardSquareIso w).hom.app ((pushforward a').obj Q) =
      (pushforwardCongr hm).hom.app Q := by
  ext U x
  simp only [pushforwardSquareIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app]
  rfl

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- The comparison of the composite direct images around a commutative square, componentwise. -/
theorem pushforwardSquareIso_app {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) (N : X'.Modules) :
    (pushforwardSquareIso w).hom.app N = (pushforwardCongr w).hom.app N := by
  ext U x
  simp only [pushforwardSquareIso, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom,
    Scheme.Modules.Hom.comp_app, pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app]
  rfl

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- The base change morphism is the mate of the comparison of the composite direct images. -/
theorem unit_comp_pushforwardSquareIso {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S}
    {g : S' ⟶ S} (w : g' ≫ f = f' ≫ g) (M : X.Modules) :
    (pushforward f).map ((pullbackPushforwardAdjunction g').unit.app M) ≫
        (pushforwardSquareIso w).hom.app ((Scheme.Modules.pullback g').obj M) =
      (pullbackPushforwardAdjunction g).unit.app ((pushforward f).obj M) ≫
        (pushforward g).map ((baseChangeNatTrans w).app M) :=
  CategoryTheory.unit_mateEquiv_symm (pullbackPushforwardAdjunction g')
    (pullbackPushforwardAdjunction g) (pushforwardSquareIso w).hom M

variable {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- The composite of `relativeUnit' h a (a' ≫ g') hk`, the comparison
`(a' ≫ g')^* ≅ a'^* g'^*` and `pushforwardSquareIso w`, all pushed forward, equals the unit of
`h^* ⊣ h_*` pushed forward along `a ≫ f`, followed by `pushforwardCongr wA` and the pushforward
of the comparison `h^* a^* M ⟶ a'^* g'^* M`. -/
theorem square_identity_left (h : A' ⟶ A) (a : A ⟶ X) (a' : A' ⟶ X') (hk : h ≫ a = a' ≫ g')
    (w : g' ≫ f = f' ≫ g) (hm : (a' ≫ g') ≫ f = (a' ≫ f') ≫ g) (wA : h ≫ a ≫ f = (a' ≫ f') ≫ g)
    (M : X.Modules) :
    (pushforward f).map ((relativeUnit' h a (a' ≫ g') hk).app M) ≫
        ((pushforward f).map ((pushforward (a' ≫ g')).map ((pullbackComp a' g').inv.app M)) ≫
          (pushforwardSquareIso w).hom.app ((pushforward a').obj
            ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M))) =
      (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforwardCongr wA).hom.app
          ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward ((a' ≫ f') ≫ g)).map ((pullbackComp h a).hom.app M ≫
          (pullbackCongr hk).hom.app M ≫ (pullbackComp a' g').inv.app M) := by
  rw [pushforwardSquareIso_app_pushforward w a'
      ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M) hm]
  exact (restriction_comp_transport h a (a' ≫ g') hk f ((a' ≫ f') ≫ g) hm wA M
    ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M)
    ((pullbackComp a' g').inv.app M))

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- The unit of `h^* ⊣ h_*` pushed forward along `a ≫ f`, followed by `pushforwardCongr wA` and
the pushforward of `e`, is the transpose under `g^* ⊣ g_*` of the base change morphism of
`wA` at `a^* M` followed by `(a' ≫ f')_* e`. -/
theorem square_identity_right (h : A' ⟶ A) (a : A ⟶ X) (a' : A' ⟶ X')
    (wA : h ≫ a ≫ f = (a' ≫ f') ≫ g) (M : X.Modules)
    (e : (Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback a).obj M) ⟶
      (Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M) :
    (pushforward (a ≫ f)).map ((pullbackPushforwardAdjunction h).unit.app
          ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforwardCongr wA).hom.app
          ((Scheme.Modules.pullback h).obj ((Scheme.Modules.pullback a).obj M)) ≫
        (pushforward ((a' ≫ f') ≫ g)).map e =
      (pullbackPushforwardAdjunction g).homEquiv ((pushforward (a ≫ f)).obj
          ((Scheme.Modules.pullback a).obj M))
        ((pushforward (a' ≫ f')).obj
          ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M))
        ((baseChangeNatTrans wA).app ((Scheme.Modules.pullback a).obj M) ≫
          (pushforward (a' ≫ f')).map e) := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rw [← unit_comp_pushforwardSquareIso, pushforwardSquareIso_app]
  exact (Category.assoc _ _ _).symm

open Stacks.AlgebraicGeometry.AffinePushforward in
/-- The composite of `relativeUnit' h a (a' ≫ g') hk`, the comparison
`(a' ≫ g')^* ≅ a'^* g'^*` and `pushforwardSquareIso w`, all pushed forward, is the transpose under
`g^* ⊣ g_*` of the base change morphism of `wA` at `a^* M` followed by the pushforward of the
comparison `h^* a^* M ⟶ a'^* g'^* M`. -/
theorem square_identity (h : A' ⟶ A) (a : A ⟶ X) (a' : A' ⟶ X') (hk : h ≫ a = a' ≫ g')
    (w : g' ≫ f = f' ≫ g) (hm : (a' ≫ g') ≫ f = (a' ≫ f') ≫ g) (wA : h ≫ a ≫ f = (a' ≫ f') ≫ g)
    (M : X.Modules) :
    (pushforward f).map ((relativeUnit' h a (a' ≫ g') hk).app M) ≫
        ((pushforward f).map ((pushforward (a' ≫ g')).map ((pullbackComp a' g').inv.app M)) ≫
          (pushforwardSquareIso w).hom.app ((pushforward a').obj
            ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M))) =
      (pullbackPushforwardAdjunction g).homEquiv ((pushforward (a ≫ f)).obj
          ((Scheme.Modules.pullback a).obj M))
        ((pushforward (a' ≫ f')).obj
          ((Scheme.Modules.pullback g' ⋙ Scheme.Modules.pullback a').obj M))
        ((baseChangeNatTrans wA).app ((Scheme.Modules.pullback a).obj M) ≫
          (pushforward (a' ≫ f')).map ((pullbackComp h a).hom.app M ≫
            (pullbackCongr hk).hom.app M ≫ (pullbackComp a' g').inv.app M)) := by
  rw [square_identity_left h a a' hk w hm wA M]
  exact square_identity_right h a a' wA M _

end Identify

end Stacks.AlgebraicGeometry.RelativeCechBaseChange
