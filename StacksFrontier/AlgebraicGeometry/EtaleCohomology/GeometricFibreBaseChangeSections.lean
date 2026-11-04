module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedPushforwardStalkSpecialization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SectionsPullbackComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkSectionsTransitivity
public import StacksCore.Tactic.StacksAttribute

/-!
# The small-étale base change map on sections, and the map to the geometric fibre

Let `f : X ⟶ S` be a morphism of schemes and `s` a geometric point of `S`. The map on abelian
sheaves

`(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`

of `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb` is *not* built from a base
change map: it is the initiality of the strict henselization among the étale neighbourhoods of
`s` followed by the counit of the inverse-image/direct-image adjunction. This file identifies its
composite with restriction to the geometric fibre `X_s` as the base change map of the cartesian
square defining `X_s`, read on global sections over `s`.

The identification rests on a description of the small-étale base change map of a commutative
square *on sections*. Restriction of sections
`Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb` carries a section of `g_*F` over an étale
object `W` of the base to a global section of `(f')⁻¹g_*F` on `X'`; the content is that applying
the base change map and reading the result on `Y` restricts the underlying section of `F` over
`X ×_S W` along the morphism `Y ⟶ X ×_S W` determined by the square.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleIdToBaseChangeIdIso` — the identity object of the small étale
  site of `Y` is the base change along `h : Y ⟶ X'` of the identity object of the small étale
  site of `X'`.
* `Stacks.EtaleCohomology.smallEtalePushforwardGammaIsoAb` — global sections of a direct image of
  abelian étale sheaves are the global sections of the sheaf itself, the abelian analogue of
  `Stacks.EtaleCohomology.smallEtalePushforwardGammaIso`.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeSquareObjHom` — the morphism of étale objects of
  `Y` along which the comparison of the two iterated direct images of a commutative square
  restricts sections.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeSquareObjHom_left_fst_fst` — that morphism is
  compatible with the projections to the étale object of the base.
* `Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_smallEtaleBaseChangeAb` — **the
  small-étale base change map on sections**: the base change map of a commutative square carries
  the restriction to `X'` of a section of `g_*F` over `W` to the restriction to `Y` of the
  underlying section of `F` over the base change of `W`, after the identification of global
  sections of `h_*` with global sections upstairs.
* `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb_comp_fibreRestrictionAb`
  — **the underived core of the last assertion of [Stacks, Tag 0GIX]**: the map from the stalk,
  followed by restriction to the geometric fibre, is the base change map of the cartesian square
  defining the geometric fibre, read on global sections over the geometric point.

## References

* [Stacks Project, Tag 0GIX](https://stacks.math.columbia.edu/tag/0GIX)
* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0GJN](https://stacks.math.columbia.edu/tag/0GJN)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### Reassociations in an abstract category -/

section Bookkeeping

variable {C : Type*} [Category C]

/-- A composite of five morphisms equals `(ue ≫ Lm) ≫ ivY`, given the commutation relations
`h1`–`h5` that move the comparison maps leftwards. -/
private theorem comp_rearrange {A₀ A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ : C}
    (u : A₀ ⟶ A₁) (ml : A₁ ⟶ A₂) (ivX : A₂ ⟶ A₃) (Gm : A₃ ⟶ A₄) (gi : A₄ ⟶ A₅)
    (m1 : A₂ ⟶ B₁) (ivX' : B₁ ⟶ A₄) (tN : B₁ ⟶ B₂) (ivY : B₂ ⟶ A₅)
    (m2 : A₁ ⟶ B₃) (hl : B₃ ⟶ B₁) (ue : A₀ ⟶ B₄) (θN : B₄ ⟶ B₃) (Lm : B₄ ⟶ B₂)
    (h1 : ivX ≫ Gm = m1 ≫ ivX') (h2 : ivX' ≫ gi = tN ≫ ivY)
    (h3 : ml ≫ m1 = m2 ≫ hl) (h4 : u ≫ m2 = ue ≫ θN) (h5 : θN ≫ hl ≫ tN = Lm) :
    (u ≫ ml) ≫ ivX ≫ Gm ≫ gi = (ue ≫ Lm) ≫ ivY := by
  simp only [Category.assoc]
  rw [← h5, ← Category.assoc ivX Gm gi, h1]
  simp only [Category.assoc]
  rw [h2, ← Category.assoc ml m1, h3]
  simp only [Category.assoc]
  rw [← Category.assoc u m2, h4]
  simp only [Category.assoc]

/-- A composite of three morphisms followed by two projections agrees with `ρ ≫ fg`, given the
factorizations `hml`, `hsq`, `hmap`, `hL`, `hi` and `hρ`. -/
private theorem comp_square_fst {A B₁ B₂ B₃ D₁ C₁ C₂ E : C}
    {ml : A ⟶ B₃} {i : A ⟶ B₁} {M : B₁ ⟶ B₂} {Q : B₂ ⟶ B₃}
    {fe : B₃ ⟶ D₁} {fg : D₁ ⟶ E} {fh : B₂ ⟶ C₁} {ff : C₁ ⟶ E}
    {f1 : B₁ ⟶ C₂} {L : C₂ ⟶ C₁} {r : C₂ ⟶ E} {hm : A ⟶ C₂} {ρ : A ⟶ D₁}
    (hml : ml = i ≫ M ≫ Q) (hsq : Q ≫ fe ≫ fg = fh ≫ ff)
    (hmap : M ≫ fh = f1 ≫ L) (hL : L ≫ ff = r) (hi : i ≫ f1 = hm)
    (hρ : ρ ≫ fg = hm ≫ r) :
    (ml ≫ fe) ≫ fg = ρ ≫ fg := by
  subst hml
  simp only [Category.assoc]
  rw [hρ, hsq, ← Category.assoc M fh, hmap, Category.assoc, hL, ← Category.assoc i f1, hi]

/-- A morphism `ml` with `ml ≫ se = 𝟙 A` composed with `fe ≫ sg` agrees with any `ρ` satisfying
`ρ ≫ sg = ee`, where `fe ≫ sg = se ≫ ee`. -/
private theorem comp_square_snd {A B₃ D₁ E : C}
    {ml : A ⟶ B₃} {fe : B₃ ⟶ D₁} {sg : D₁ ⟶ E} {se : B₃ ⟶ A} {ee : A ⟶ E} {ρ : A ⟶ D₁}
    (hcond : fe ≫ sg = se ≫ ee) (hover : ml ≫ se = 𝟙 A) (hρ : ρ ≫ sg = ee) :
    (ml ≫ fe) ≫ sg = ρ ≫ sg := by
  rw [hρ, Category.assoc, hcond, ← Category.assoc, hover, Category.id_comp]

/-- A composite of two morphisms followed by a projection, unwound through two factorizations
whose middle terms are composites. -/
private theorem comp_fst_chain {A B D E A₁ A₂ A₃ : C}
    {c : A ⟶ B} {l : B ⟶ D} {p : D ⟶ E} {a : B ⟶ A₁} {b : A₁ ⟶ E}
    {x : A ⟶ A₂} {y : A₂ ⟶ A₁} {z : A₂ ⟶ E} {ρ : A ⟶ A₃} {q : A₃ ⟶ E}
    (h1 : l ≫ p = a ≫ b) (h2 : c ≫ a = x ≫ y) (h3 : y ≫ b = z) (h4 : ρ ≫ q = x ≫ z) :
    (c ≫ l) ≫ p = ρ ≫ q := by
  rw [h4, Category.assoc, h1, ← Category.assoc, h2, Category.assoc, h3]

/-- A composite of two morphisms followed by a projection, unwound through two factorizations
whose middle terms are single morphisms. -/
private theorem comp_snd_chain {A B D E A₃ : C} {c : A ⟶ B} {l : B ⟶ D} {p : D ⟶ E}
    {m : B ⟶ E} {n : A ⟶ E} {ρ : A ⟶ A₃} {q : A₃ ⟶ E}
    (h1 : l ≫ p = m) (h2 : c ≫ m = n) (h3 : ρ ≫ q = n) :
    (c ≫ l) ≫ p = ρ ≫ q := by
  rw [h3, Category.assoc, h1, h2]

/-- If `t ≫ a = a'` and `a' ≫ b = r`, then `t ≫ a ≫ b = r`. -/
private theorem germ_comp₂ {A₀ A₁ A₂ A₃ : C} (t : A₀ ⟶ A₁) (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃)
    {a' : A₀ ⟶ A₂} {r : A₀ ⟶ A₃} (h1 : t ≫ a = a') (h2 : a' ≫ b = r) :
    t ≫ a ≫ b = r := by
  rw [← Category.assoc, h1, h2]

/-- If `α ≫ q = 𝟙` and `q ≫ p = 𝟙`, then `α = p`. -/
private theorem eq_of_comp_cancel {A₀ A₁ : C} {α p : A₀ ⟶ A₁} {q : A₁ ⟶ A₀}
    (h1 : α ≫ q = 𝟙 A₀) (h2 : q ≫ p = 𝟙 A₁) : α = p := by
  rw [← Category.comp_id α, ← h2, ← Category.assoc, h1, Category.id_comp]

/-- If `t = hm ≫ 𝟙 A₀ ≫ k` and `iv ≫ hm = 𝟙 A₀`, then `iv ≫ t = k`. -/
private theorem inv_hom_id_comp {A₀ A₁ A₂ : C} {iv : A₀ ⟶ A₁} {hm : A₁ ⟶ A₀}
    {k : A₀ ⟶ A₂} {t : A₁ ⟶ A₂}
    (ht : t = hm ≫ 𝟙 A₀ ≫ k) (hid : iv ≫ hm = 𝟙 A₀) :
    iv ≫ t = k := by
  rw [ht, Category.id_comp, ← Category.assoc, hid, Category.id_comp]

end Bookkeeping

section Bookkeeping

/-- A functor carries a composite of three morphisms to the composite of their images. -/
private theorem map_comp_triple {D E : Type*} [Category D] [Category E] (N : D ⥤ E)
    {A B₁ B₂ B₃ : D} (q : A ⟶ B₁) (m : B₁ ⟶ B₂) (i : B₂ ⟶ B₃) {l : A ⟶ B₃}
    (hl : q ≫ m ≫ i = l) :
    N.map q ≫ N.map m ≫ N.map i = N.map l := by
  rw [← N.map_comp, ← N.map_comp, hl]

/-- Passing a composite of three morphisms to the opposite category reverses it. -/
private theorem op_comp_triple {D : Type*} [Category D] {A B₁ B₂ B₃ : D}
    (i : A ⟶ B₁) (m : B₁ ⟶ B₂) (q : B₂ ⟶ B₃) {l : A ⟶ B₃} (hl : i ≫ m ≫ q = l) :
    q.op ≫ m.op ≫ i.op = l.op := by
  rw [← op_comp, ← op_comp, ← hl, Category.assoc]

end Bookkeeping

/-! ### Unfolding restriction of sections and direct images -/

section Unfold

/-- Restriction of sections of an abelian étale sheaf over an étale object to global sections of
an inverse image is the unit of the inverse-image/direct-image adjunction, restricted along the
chosen lift into the base change and read as a global section. -/
theorem smallEtaleSectionsPullbackAb_app {Z T : Scheme.{u}} (p : T ⟶ Z) (W : Z.Etale)
    (r : T ⟶ W.left) (hr : r ≫ W.hom = p) (M : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtaleSectionsPullbackAb p W r hr).app M =
      (((smallEtaleAdjunctionAb p).unit.app M).hom.app (op W) ≫
          ((smallEtalePullbackAb p).obj M).obj.map (smallEtaleBaseChangeLift p W r hr).op) ≫
        (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology T) Ab.{u + 1}
          (isTerminalEtaleMkId T)).inv.app ((smallEtalePullbackAb p).obj M) :=
  rfl

/-- Direct image of abelian étale sheaves is restriction along the base-change functor, so on
sections over an étale object it carries a morphism of sheaves to its component at the base
change of that object. -/
theorem smallEtalePushforwardAb_map_hom_app {X Y : Scheme.{u}} (k : X ⟶ Y)
    {M N : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : M ⟶ N) (W : Y.Etale) :
    ((smallEtalePushforwardAb k).map φ).hom.app (op W) =
      φ.hom.app (op ((smallEtaleBaseChange k).obj W)) :=
  rfl

/-- The composition isomorphism for direct image of abelian étale sheaves is, on sections over an
étale object of the target, restriction along the comparison of the base change along the
composite with the iterated base change. -/
theorem smallEtalePushforwardAbCompIso_hom_app_hom_app {X X' T : Scheme.{u}} (a : T ⟶ X')
    (b : X' ⟶ X) (M : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (W : X.Etale) :
    ((smallEtalePushforwardAbCompIso a b).hom.app M).hom.app (op W) =
      M.obj.map ((smallEtaleBaseChangeComp a b).hom.app W).op := by
  have hqp : M.obj.map ((smallEtaleBaseChangeComp a b).inv.app W).op ≫
      M.obj.map ((smallEtaleBaseChangeComp a b).hom.app W).op =
      𝟙 (M.obj.obj (op ((smallEtaleBaseChange (a ≫ b)).obj W))) := by
    rw [← M.obj.map_comp, ← op_comp, Iso.hom_inv_id_app, op_id, M.obj.map_id]
  exact eq_of_comp_cancel
    (q := ((smallEtalePushforwardAbCompIso a b).inv.app M).hom.app (op W))
    (congrArg (fun φ => φ.hom.app (op W))
      (Iso.hom_inv_id_app (smallEtalePushforwardAbCompIso a b) M))
    ((congrArg (fun z => z ≫ M.obj.map ((smallEtaleBaseChangeComp a b).hom.app W).op)
      (smallEtalePushforwardAbCompIso_inv_app_hom_app a b M W)).trans hqp)

/-- Transport of a direct image of abelian étale sheaves along an equality of morphisms of
schemes is, on sections over an étale object, restriction along the induced identification of the
two base changes of that object. -/
theorem smallEtalePushforwardAb_eqToIso_hom_app_hom_app {Y S : Scheme.{u}} {a b : Y ⟶ S}
    (hab : a = b) (N : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (W : S.Etale)
    (m : (smallEtaleBaseChange b).obj W ⟶ (smallEtaleBaseChange a).obj W)
    (hm : m = eqToHom (congrArg (fun k : Y ⟶ S =>
      (smallEtaleBaseChange k).obj W) hab).symm) :
    ((eqToIso (congrArg smallEtalePushforwardAb hab)).hom.app N).hom.app (op W) =
      N.obj.map m.op := by
  subst hab hm
  exact (N.obj.map_id (op ((smallEtaleBaseChange a).obj W))).symm

/-- The identification of the two base changes of an étale object induced by an equality of
morphisms of schemes is compatible with the projections to that object. -/
theorem eqToHom_smallEtaleBaseChange_left_fst {Y S : Scheme.{u}} {a b : Y ⟶ S} (hab : a = b)
    (W : S.Etale) :
    (eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj W) hab)).left ≫
        pullback.fst W.hom b = pullback.fst W.hom a := by
  subst hab
  exact Category.id_comp _

end Unfold

/-! ### Global sections of a direct image of abelian sheaves -/

section PushforwardGamma

variable {X' Y : Scheme.{u}} (h : Y ⟶ X')

/-- **The base change of the identity object is the identity object.** The identity object of the
small étale site of `Y` is isomorphic to the base change along `h : Y ⟶ X'` of the identity
object of the small étale site of `X'`, by the lift determined by `h` itself. -/
def smallEtaleIdToBaseChangeIdIso :
    Scheme.Etale.mk (𝟙 Y) ≅ (smallEtaleBaseChange h).obj (Scheme.Etale.mk (𝟙 X')) where
  hom := smallEtaleBaseChangeLift h (Scheme.Etale.mk (𝟙 X')) h (Category.comp_id h)
  inv := (isTerminalEtaleMkId Y).from _
  hom_inv_id := (isTerminalEtaleMkId Y).hom_ext _ _
  inv_hom_id := (isTerminalSmallEtaleBaseChangeObj h (isTerminalEtaleMkId X')).hom_ext _ _

/-- The isomorphism of identity objects is, on underlying schemes, the morphism into the fibre
product with components `h` and the identity, so its first projection is `h`. -/
theorem smallEtaleIdToBaseChangeIdIso_hom_left_fst :
    (smallEtaleIdToBaseChangeIdIso h).hom.left ≫ pullback.fst (𝟙 X') h = h :=
  pullback.lift_fst _ _ _

/-- **Global sections of a direct image of abelian étale sheaves are the global sections of the
sheaf itself.** For an abelian étale sheaf `G` on `Y`, the global sections of `h_*G` are
identified with the global sections of `G`. -/
def smallEtalePushforwardGammaIsoAb :
    smallEtalePushforwardAb h ⋙ Sheaf.Γ (smallEtaleTopology X') Ab.{u + 1} ≅
      Sheaf.Γ (smallEtaleTopology Y) Ab.{u + 1} :=
  Functor.isoWhiskerLeft (smallEtalePushforwardAb h)
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X') Ab.{u + 1}
        (isTerminalEtaleMkId X')) ≪≫
    NatIso.ofComponents (fun _ ↦ Iso.refl _) ≪≫
    (sheafSections (smallEtaleTopology Y) Ab.{u + 1}).mapIso
      (smallEtaleIdToBaseChangeIdIso h).op ≪≫
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
      (isTerminalEtaleMkId Y)).symm

/-- The identification of global sections of a direct image with the global sections upstairs is,
read through the identifications of global sections with sections over the identity objects,
restriction along the isomorphism of identity objects. -/
theorem smallEtalePushforwardGammaIsoAb_hom_app
    (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) :
    (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X') Ab.{u + 1}
          (isTerminalEtaleMkId X')).inv.app ((smallEtalePushforwardAb h).obj G) ≫
        (smallEtalePushforwardGammaIsoAb h).hom.app G =
      G.obj.map (smallEtaleIdToBaseChangeIdIso h).hom.op ≫
        (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
          (isTerminalEtaleMkId Y)).inv.app G := by
  have hhom : (smallEtalePushforwardGammaIsoAb h).hom.app G =
      (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X') Ab.{u + 1}
            (isTerminalEtaleMkId X')).hom.app ((smallEtalePushforwardAb h).obj G) ≫
        𝟙 (((sheafSections (smallEtaleTopology X') Ab.{u + 1}).obj
            (op (Scheme.Etale.mk (𝟙 X')))).obj ((smallEtalePushforwardAb h).obj G)) ≫
          G.obj.map (smallEtaleIdToBaseChangeIdIso h).hom.op ≫
            (Sheaf.ΓNatIsoSheafSections (smallEtaleTopology Y) Ab.{u + 1}
              (isTerminalEtaleMkId Y)).inv.app G := rfl
  exact inv_hom_id_comp hhom (Iso.inv_hom_id_app _ _)

end PushforwardGamma

/-! ### The comparison of the two iterated direct images of a square, on sections -/

section Square

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The morphism of étale objects of `Y` along which the comparison of the two iterated direct
images of a commutative square restricts sections over an étale object `W` of the base: the
comparison of the iterated base change along `h` and `f'` with the base change along `h ≫ f'`,
the transport along the commutativity of the square, and the comparison of the base change along
`e ≫ g` with the iterated base change along `e` and `g`. -/
def smallEtaleBaseChangeSquareObjHom (W : S.Etale) :
    (smallEtaleBaseChange h).obj ((smallEtaleBaseChange f').obj W) ⟶
      (smallEtaleBaseChange e).obj ((smallEtaleBaseChange g).obj W) :=
  (smallEtaleBaseChangeComp h f').inv.app W ≫
    eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj W) w) ≫
    (smallEtaleBaseChangeComp e g).hom.app W

/-- The morphism of étale objects attached to a commutative square is compatible with the
projections to the étale object of the base: on first projections it is the projection down the
one side of the square followed by the projection along the other. -/
theorem smallEtaleBaseChangeSquareObjHom_left_fst_fst (W : S.Etale) :
    (smallEtaleBaseChangeSquareObjHom f' g h e w W).left ≫
        pullback.fst ((smallEtaleBaseChange g).obj W).hom e ≫ pullback.fst W.hom g =
      pullback.fst ((smallEtaleBaseChange f').obj W).hom h ≫ pullback.fst W.hom f' := by
  have hleft : (smallEtaleBaseChangeSquareObjHom f' g h e w W).left =
      ((smallEtaleBaseChangeComp h f').inv.app W).left ≫
        (eqToHom (congrArg (fun k : Y ⟶ S =>
          (smallEtaleBaseChange k).obj W) w)).left ≫
        ((smallEtaleBaseChangeComp e g).hom.app W).left := rfl
  rw [hleft]
  simp only [Category.assoc]
  rw [smallEtaleBaseChangeComp_hom_app_left_fst_fst e g W,
    eqToHom_smallEtaleBaseChange_left_fst w W, smallEtaleBaseChangeComp_inv_app_left_fst h f' W]
  rfl

/-- The comparison of the two iterated direct images of a commutative square is, on sections over
an étale object of the base, restriction along
`Stacks.EtaleCohomology.smallEtaleBaseChangeSquareObjHom`. -/
theorem smallEtalePushforwardAbSquareIso_hom_app_hom_app
    (N : Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (W : S.Etale) :
    (((smallEtalePushforwardAbCompIso e g).trans
            ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
              (smallEtalePushforwardAbCompIso h f').symm)).hom.app N).hom.app (op W) =
      N.obj.map (smallEtaleBaseChangeSquareObjHom f' g h e w W).op := by
  have heq := smallEtalePushforwardAb_eqToIso_hom_app_hom_app w.symm N W
    (eqToHom (congrArg (fun k : Y ⟶ S => (smallEtaleBaseChange k).obj W) w)) rfl
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    ObjectProperty.FullSubcategory.comp_hom]
  rw [smallEtalePushforwardAbCompIso_hom_app_hom_app, heq,
    smallEtalePushforwardAbCompIso_inv_app_hom_app, smallEtaleBaseChangeSquareObjHom]
  simp only [op_comp, N.obj.map_comp, Category.assoc]
  rfl

end Square

/-! ### The small-étale base change map on sections -/

section BaseChangeSections

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The defining adjoint identity of the small-étale base change map of a commutative square:
transposed under the adjunction for `f'`, it is the unit of the adjunction for `e` followed by
the comparison of the two iterated direct images. -/
theorem unit_comp_smallEtaleBaseChangeAb_app
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtaleAdjunctionAb f').unit.app ((smallEtalePushforwardAb g).obj F) ≫
        (smallEtalePushforwardAb f').map ((smallEtaleBaseChangeAb f' g h e w).app F) =
      (smallEtalePushforwardAb g).map ((smallEtaleAdjunctionAb e).unit.app F) ≫
        ((smallEtalePushforwardAbCompIso e g).trans
            ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
              (smallEtalePushforwardAbCompIso h f').symm)).hom.app
          ((smallEtalePullbackAb e).obj F) := by
  have hdef : smallEtaleBaseChangeAb f' g h e w =
      Stacks.Cohomology.BaseChange.mate (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e)
        (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        ((smallEtalePushforwardAbCompIso e g).trans
          ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
            (smallEtalePushforwardAbCompIso h f').symm)) := rfl
  rw [hdef]
  exact Stacks.Cohomology.BaseChange.unit_comp_map_mate (smallEtaleAdjunctionAb f')
    (smallEtaleAdjunctionAb e) (smallEtalePushforwardAb g) (smallEtalePushforwardAb h) _ F

/-- **The small-étale base change map on sections.** Let

```
Y  --h-->  X'
|e         |f'
T  --g-->  S
```

be a commutative square of schemes, `W` an étale object of `S` and `r : X' ⟶ W` a morphism lying
over `f'`. Restricting a section of `g_*F` over `W` to a global section of `(f')⁻¹g_*F` on `X'`
along `r`, applying the base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` and reading the result as a global section on
`Y`, is restricting the underlying section of `F` over the base change `T ×_S W` along the
morphism `ρ : Y ⟶ T ×_S W` with components `h ≫ r` and `e`. -/
theorem smallEtaleSectionsPullbackAb_comp_smallEtaleBaseChangeAb
    (W : S.Etale) (r : X' ⟶ W.left) (hr : r ≫ W.hom = f')
    (ρ : Y ⟶ ((smallEtaleBaseChange g).obj W).left)
    (hρ : ρ ≫ ((smallEtaleBaseChange g).obj W).hom = e)
    (hfst : ρ ≫ pullback.fst W.hom g = h ≫ r) :
    Functor.whiskerLeft (smallEtalePushforwardAb g)
          (smallEtaleSectionsPullbackAb f' W r hr) ≫
        Functor.whiskerRight (smallEtaleBaseChangeAb f' g h e w)
          (Sheaf.Γ (smallEtaleTopology X') Ab.{u + 1}) ≫
        Functor.whiskerLeft (smallEtalePullbackAb e)
          (smallEtalePushforwardGammaIsoAb h).hom =
      smallEtaleSectionsPullbackAb e ((smallEtaleBaseChange g).obj W) ρ hρ := by
  refine NatTrans.ext (funext fun F => ?_)
  have hgeom : (smallEtaleIdToBaseChangeIdIso h).hom ≫
        (smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr) ≫
          smallEtaleBaseChangeSquareObjHom f' g h e w W =
      smallEtaleBaseChangeLift e ((smallEtaleBaseChange g).obj W) ρ hρ := by
    refine smallEtaleBaseChangeLift_eq e ((smallEtaleBaseChange g).obj W) ρ hρ _ ?_
    have hover : ((smallEtaleIdToBaseChangeIdIso h).hom ≫
        (smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr) ≫
          smallEtaleBaseChangeSquareObjHom f' g h e w W).left ≫
        pullback.snd ((smallEtaleBaseChange g).obj W).hom e = 𝟙 Y :=
      MorphismProperty.Over.w _
    have hmapfst : ((smallEtaleBaseChange h).map
          (smallEtaleBaseChangeLift f' W r hr)).left ≫
        pullback.fst ((smallEtaleBaseChange f').obj W).hom h =
      pullback.fst (Scheme.Etale.mk (𝟙 X')).hom h ≫
        (smallEtaleBaseChangeLift f' W r hr).left := pullback.lift_fst _ _ _
    have hliftfst : (smallEtaleBaseChangeLift f' W r hr).left ≫ pullback.fst W.hom f' = r :=
      pullback.lift_fst _ _ _
    have hidfst : (smallEtaleIdToBaseChangeIdIso h).hom.left ≫
        pullback.fst (Scheme.Etale.mk (𝟙 X')).hom h = h :=
      smallEtaleIdToBaseChangeIdIso_hom_left_fst h
    have hleft : ((smallEtaleIdToBaseChangeIdIso h).hom ≫
          (smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr) ≫
            smallEtaleBaseChangeSquareObjHom f' g h e w W).left =
        (smallEtaleIdToBaseChangeIdIso h).hom.left ≫
          ((smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr)).left ≫
          (smallEtaleBaseChangeSquareObjHom f' g h e w W).left := rfl
    refine pullback.hom_ext ?_ ?_
    · exact comp_square_fst hleft
        (smallEtaleBaseChangeSquareObjHom_left_fst_fst f' g h e w W)
        hmapfst hliftfst hidfst hfst
    · exact comp_square_snd pullback.condition hover hρ
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    smallEtaleSectionsPullbackAb_app, Category.assoc]
  refine comp_rearrange _ _ _ _ _
    (((smallEtaleBaseChangeAb f' g h e w).app F).hom.app (op (Scheme.Etale.mk (𝟙 X'))))
    ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X') Ab.{u + 1}
      (isTerminalEtaleMkId X')).inv.app
        ((smallEtalePushforwardAb h).obj ((smallEtalePullbackAb e).obj F)))
    (((smallEtalePullbackAb e).obj F).obj.map (smallEtaleIdToBaseChangeIdIso h).hom.op)
    _
    (((smallEtaleBaseChangeAb f' g h e w).app F).hom.app
      (op ((smallEtaleBaseChange f').obj W)))
    (((smallEtalePullbackAb e).obj F).obj.map
      ((smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr)).op)
    _
    (((smallEtalePullbackAb e).obj F).obj.map
      (smallEtaleBaseChangeSquareObjHom f' g h e w W).op)
    _ ?_ ?_ ?_ ?_ ?_
  · exact ((Sheaf.ΓNatIsoSheafSections (smallEtaleTopology X') Ab.{u + 1}
      (isTerminalEtaleMkId X')).inv.naturality
        ((smallEtaleBaseChangeAb f' g h e w).app F)).symm
  · exact smallEtalePushforwardGammaIsoAb_hom_app h ((smallEtalePullbackAb e).obj F)
  · exact (((smallEtaleBaseChangeAb f' g h e w).app F).hom.naturality
      (smallEtaleBaseChangeLift f' W r hr).op)
  · have key := congrArg (fun φ => φ.hom.app (op W))
      (unit_comp_smallEtaleBaseChangeAb_app f' g h e w F)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      smallEtalePushforwardAb_map_hom_app] at key
    rwa [smallEtalePushforwardAbSquareIso_hom_app_hom_app] at key
  · exact map_comp_triple ((smallEtalePullbackAb e).obj F).obj
      (smallEtaleBaseChangeSquareObjHom f' g h e w W).op
      ((smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr)).op
      (smallEtaleIdToBaseChangeIdIso h).hom.op
      (op_comp_triple (smallEtaleIdToBaseChangeIdIso h).hom
        ((smallEtaleBaseChange h).map (smallEtaleBaseChangeLift f' W r hr))
        (smallEtaleBaseChangeSquareObjHom f' g h e w W) hgeom)

end BaseChangeSections

end Stacks.EtaleCohomology

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

/-! ### The map from the stalk and the base change map of the geometric fibre -/

section Fibre

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hS : B.Contains S) (f : X ⟶ S)
  (s : GeometricPoint S)

/-- The canonical morphism from the geometric fibre to the base change to the strict
henselization lies over the strict henselization: its second projection is the structure morphism
of the fibre followed by the canonical lift of the geometric point. -/
theorem geometricFibreToStrictHenselizationBaseChange_comp_toStrictHenselization :
    geometricFibreToStrictHenselizationBaseChange B hS f s ≫
        strictHenselizationBaseChangeToStrictHenselization B hS f s =
      geometricFibreToPoint f s ≫ geometricPointToStrictHenselization B S hS s :=
  pullback.lift_snd _ _ _

/-- For `f : X ⟶ S` a morphism of schemes, `s` a geometric point of `S` and `F` an abelian sheaf
on the small étale site of `X`, the canonical map

`(f_*F)_s ⟶ Γ(X ×_S Spec(𝒪^{sh}_{S,s}), p⁻¹F)`

of `AlgebraicGeometry.pushforwardStalkToStrictHenselizationSectionsAb`, followed by restriction
of sections to the geometric fibre `X_s`, is the base change map of the cartesian square defining
`X_s` read on global sections over `s`: the comparison
`AlgebraicGeometry.geometricStalkToPullbackSectionsAb` of the stalk at `s` with global sections
on `s` of the inverse image, the base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` of the square, and the identification
`Stacks.EtaleCohomology.smallEtalePushforwardGammaIsoAb` of global sections of a direct image
with the global sections upstairs. -/
theorem pushforwardStalkToStrictHenselizationSectionsAb_comp_fibreRestrictionAb :
    pushforwardStalkToStrictHenselizationSectionsAb B hS f s ≫
        smallEtaleSectionsRestrictionAb (strictHenselizationBaseChangeToSource B hS f s)
          (geometricFibreToStrictHenselizationBaseChange B hS f s)
          (geometricFibreToSource f s)
          (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s) =
      Functor.whiskerLeft (smallEtalePushforwardAb f)
          (geometricStalkToPullbackSectionsAb s.hom) ≫
        Functor.whiskerRight
          (smallEtaleBaseChangeAb s.hom f (geometricFibreToPoint f s)
            (geometricFibreToSource f s) pullback.condition.symm)
          (Sheaf.Γ (smallEtaleTopology s.source) Ab.{u + 1}) ≫
        Functor.whiskerLeft (smallEtalePullbackAb (geometricFibreToSource f s))
          (smallEtalePushforwardGammaIsoAb (geometricFibreToPoint f s)).hom := by
  refine NatTrans.ext (funext fun F => ?_)
  refine smallEtaleStalkAb_hom_ext s.hom ((smallEtalePushforwardAb f).obj F) fun W v => ?_
  have hρcond : (geometricFibreToPoint f s ≫ v.left) ≫ W.hom =
      geometricFibreToSource f s ≫ f :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun y : s.source ⟶ S => geometricFibreToPoint f s ≫ y) (Over.w v)).trans
        pullback.condition.symm)
  have hρfst : pullback.lift (geometricFibreToPoint f s ≫ v.left)
        (geometricFibreToSource f s) hρcond ≫ pullback.fst W.hom f =
      geometricFibreToPoint f s ≫ v.left := pullback.lift_fst _ _ _
  have hρsnd : pullback.lift (geometricFibreToPoint f s ≫ v.left)
        (geometricFibreToSource f s) hρcond ≫ ((smallEtaleBaseChange f).obj W).hom =
      geometricFibreToSource f s := pullback.lift_snd _ _ _
  have hliftfst : strictHenselizationBaseChangeEtaleLift B hS f s W v ≫ pullback.fst W.hom f =
      strictHenselizationBaseChangeToStrictHenselization B hS f s ≫
        strictHenselizationNeighborhoodLift B S hS s W v := pullback.lift_fst _ _ _
  have hliftsnd : strictHenselizationBaseChangeEtaleLift B hS f s W v ≫
        ((smallEtaleBaseChange f).obj W).hom =
      strictHenselizationBaseChangeToSource B hS f s := pullback.lift_snd _ _ _
  have hcr : geometricFibreToStrictHenselizationBaseChange B hS f s ≫
        strictHenselizationBaseChangeEtaleLift B hS f s W v =
      pullback.lift (geometricFibreToPoint f s ≫ v.left)
        (geometricFibreToSource f s) hρcond := by
    refine pullback.hom_ext ?_ ?_
    · exact comp_fst_chain hliftfst
        (geometricFibreToStrictHenselizationBaseChange_comp_toStrictHenselization B hS f s)
        (geometricPointToStrictHenselization_comp_neighborhoodLift B S hS s W v) hρfst
    · exact comp_snd_chain hliftsnd
        (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s) hρsnd
  have hlhs := pushforwardStalkToStrictHenselizationSectionsAb_toPresheafFiber B hS f s W v F
  have hfinal := congrArg (fun φ => NatTrans.app φ F)
    (Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_sectionsRestrictionAb
      (strictHenselizationBaseChangeToSource B hS f s) ((smallEtaleBaseChange f).obj W)
      (geometricFibreToStrictHenselizationBaseChange B hS f s) (geometricFibreToSource f s)
      (strictHenselizationBaseChangeEtaleLift B hS f s W v) hliftsnd
      (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s)
      (pullback.lift (geometricFibreToPoint f s ≫ v.left)
        (geometricFibreToSource f s) hρcond) hρsnd hcr)
  have hgerm := geometricStalkToPullbackSectionsAb_toPresheafFiber s.hom
    ((smallEtalePushforwardAb f).obj F) W v
  have hbc := congrArg (fun φ => NatTrans.app φ F)
    (Stacks.EtaleCohomology.smallEtaleSectionsPullbackAb_comp_smallEtaleBaseChangeAb s.hom f
      (geometricFibreToPoint f s) (geometricFibreToSource f s) pullback.condition.symm W
      v.left (Over.w v)
      (pullback.lift (geometricFibreToPoint f s ≫ v.left)
        (geometricFibreToSource f s) hρcond) hρsnd hρfst)
  refine Eq.trans (b := (smallEtaleSectionsPullbackAb (geometricFibreToSource f s)
    ((smallEtaleBaseChange f).obj W)
    (pullback.lift (geometricFibreToPoint f s ≫ v.left)
      (geometricFibreToSource f s) hρcond) hρsnd).app F) ?_ ?_
  · exact germ_comp₂ _
      ((pushforwardStalkToStrictHenselizationSectionsAb B hS f s).app F)
      ((smallEtaleSectionsRestrictionAb (strictHenselizationBaseChangeToSource B hS f s)
        (geometricFibreToStrictHenselizationBaseChange B hS f s)
        (geometricFibreToSource f s)
        (geometricFibreToStrictHenselizationBaseChange_comp_toSource B hS f s)).app F)
      hlhs hfinal
  · exact (germ_comp₂ _
      ((geometricStalkToPullbackSectionsAb s.hom).app ((smallEtalePushforwardAb f).obj F)) _
      hgerm hbc).symm

end Fibre

end AlgebraicGeometry

end
