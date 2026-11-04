module

public import StacksFrontier.AlgebraicGeometry.CompactOpenInduction.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# Derived pullbacks along factorisations and the system of derived morphism sets

This file contains the first part of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom`: the comparison morphisms of
derived pullbacks along factorisations and commutative squares of morphisms of ringed spaces and
of schemes, the factorisations of the transition and projection morphisms of a relative descent
situation, the directed system of derived morphism sets with its colimit comparison
(`HomDescent`), and the restriction of a relative descent situation to a quasi-compact open of
the fixed stage (`RestrictHomDescent`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.Cohomology.DerivedPushforwardAssociativity (derivedPullbackCompIsoCanonical_assoc
  derivedPullbackIdIso derivedPullbackCompIsoCanonical_id_comp)

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.DerivedPullback

/-! ### Derived pullback along a factorisation -/

section RingedSpaces

variable {V W X Y Z : RingedSpace.{u, u}}

/-- The comparison isomorphism `Lg^* ⋙ Lf^* ≅ Lk^*` attached to a factorisation `f ≫ g = k` of
morphisms of ringed spaces. -/
def factorIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    ∀ (k : X ⟶ Z), f ≫ g = k →
      (derivedPullback g ⋙ derivedPullback f ≅ derivedPullback k)
  | _, rfl => derivedPullbackCompIsoCanonical f g

/-- The map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Lk^*K, Lk^*L)` induced by a factorisation `f ≫ g = k`: apply
`Lf^*` and transport along `factorIso`. -/
def factorHom (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    (derivedPullback k).obj K ⟶ (derivedPullback k).obj L :=
  ((factorIso f g k h).app K).homCongr ((factorIso f g k h).app L) ((derivedPullback f).map φ)

/-- The comparison isomorphisms of the factorisations of `c = p ≫ t ≫ a` satisfy the cocycle
identity. -/
theorem factorIso_assoc (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z)
    (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (factorIso p t q hq).app ((derivedPullback a).obj M) ≪≫ (factorIso q a c hc).app M =
      (derivedPullback p).mapIso ((factorIso t a b hb).app M) ≪≫
        (factorIso p b c hpb).app M := by
  subst hb; subst hq; subst hc
  refine Iso.ext ?_
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  exact Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackCompIsoCanonical_assoc_app
    p t a M

/-- Transporting the map induced by the inner factorisation `p ≫ t = q` along `q ≫ a = c` gives
the map induced by `p ≫ b = c` after transport along `t ≫ a = b`. -/
private theorem homCongr_factorIso_factorHom (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z)
    (q : V ⟶ Y) (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c)
    (hpb : p ≫ b = c) (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (ψ : (derivedPullback t).obj ((derivedPullback a).obj K) ⟶
      (derivedPullback t).obj ((derivedPullback a).obj L)) :
    ((factorIso q a c hc).app K).homCongr ((factorIso q a c hc).app L)
        (factorHom p t q hq ((derivedPullback a).obj K) ((derivedPullback a).obj L) ψ) =
      factorHom p b c hpb K L
        (((factorIso t a b hb).app K).homCongr ((factorIso t a b hb).app L) ψ) := by
  have hK := congrArg Iso.inv (factorIso_assoc p t a b q c hb hq hc hpb K)
  have hL := congrArg Iso.hom (factorIso_assoc p t a b q c hb hq hc hpb L)
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_inv] at hK hL
  simp only [factorHom, Iso.homCongr_apply, Functor.map_comp, Category.assoc]
  rw [← hL]
  rw [reassoc_of% hK]

/-- The maps on derived Hom induced by the factorisations of `c = p ≫ t ≫ a` compose. -/
theorem factorHom_comp (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y) (c : V ⟶ Z)
    (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback a).obj K ⟶ (derivedPullback a).obj L) :
    factorHom p b c hpb K L (factorHom t a b hb K L φ) = factorHom q a c hc K L φ := by
  have h := homCongr_factorIso_factorHom p t a b q c hb hq hc hpb K L ((derivedPullback t).map φ)
  have nat : factorHom p t q hq ((derivedPullback a).obj K) ((derivedPullback a).obj L)
      ((derivedPullback t).map φ) = (derivedPullback q).map φ := by
    rw [factorHom, Iso.homCongr_apply, Iso.inv_comp_eq]
    exact (factorIso p t q hq).hom.naturality φ
  rw [nat] at h
  exact h.symm

/-- A three-factor composite followed by an identity collapses to `φ` when its last two factors
factor through `φ` and the first two cancel. -/
private theorem comp_three_comp_id {E : Type*} [Category E] {A B C D : E}
    {u : A ⟶ B} {m : B ⟶ C} {v : C ⟶ D} {w : B ⟶ A} {φ : A ⟶ D}
    (h1 : m ≫ v = w ≫ φ) (h2 : u ≫ w = 𝟙 A) :
    u ≫ m ≫ v ≫ 𝟙 D = φ := by
  rw [Category.comp_id, h1, ← Category.assoc, h2, Category.id_comp]

/-- The comparison isomorphism attached to the factorisation `𝟙 ≫ a = a` is
`derivedPullbackCompIsoCanonical (𝟙 X) a`. -/
theorem factorIso_id (a : X ⟶ Z) (h : 𝟙 X ≫ a = a) :
    factorIso (𝟙 X) a a h = derivedPullbackCompIsoCanonical (𝟙 X) a :=
  rfl

/-- The map on derived Hom induced by a factorisation through an identity is the identity. -/
theorem factorHom_id {f : X ⟶ X} (hf : f = 𝟙 X) (a : X ⟶ Z) (h : f ≫ a = a)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback a).obj K ⟶ (derivedPullback a).obj L) :
    factorHom f a a h K L φ = φ := by
  subst hf
  simp only [factorHom, factorIso_id, derivedPullbackCompIsoCanonical_id_comp,
    Iso.homCongr_apply, Iso.app_inv, Iso.app_hom, Iso.trans_inv, Iso.trans_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Category.id_comp]
  exact comp_three_comp_id ((derivedPullbackIdIso X).hom.naturality φ)
    ((derivedPullbackIdIso X).inv_hom_id_app _)

end RingedSpaces

/-! ### Derived pullback along a factorisation of morphisms of schemes -/

section Schemes

variable {V W X Y Z : Scheme.{u}}

/-- The comparison isomorphism `Lg^* ⋙ Lf^* ≅ Lk^*` attached to a factorisation `f ≫ g = k` of
morphisms of schemes. -/
def schemeFactorIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k) :
    derivedPullback g.toLRSHom.toShHom ⋙ derivedPullback f.toLRSHom.toShHom ≅
      derivedPullback k.toLRSHom.toShHom :=
  factorIso f.toLRSHom.toShHom g.toLRSHom.toShHom k.toLRSHom.toShHom
    (congrArg (fun m : X ⟶ Z ↦ m.toLRSHom.toShHom) h)

/-- The map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Lk^*K, Lk^*L)` induced by a factorisation `f ≫ g = k` of
morphisms of schemes. -/
def schemeFactorHom (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    (derivedPullback k.toLRSHom.toShHom).obj K ⟶ (derivedPullback k.toLRSHom.toShHom).obj L :=
  ((schemeFactorIso f g k h).app K).homCongr ((schemeFactorIso f g k h).app L)
    ((derivedPullback f.toLRSHom.toShHom).map φ)

/-- The maps on derived Hom induced by the factorisations of `c = p ≫ t ≫ a` compose. -/
theorem schemeFactorHom_comp (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y)
    (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback a.toLRSHom.toShHom).obj K ⟶
      (derivedPullback a.toLRSHom.toShHom).obj L) :
    schemeFactorHom p b c hpb K L (schemeFactorHom t a b hb K L φ) =
      schemeFactorHom q a c hc K L φ :=
  factorHom_comp p.toLRSHom.toShHom t.toLRSHom.toShHom a.toLRSHom.toShHom b.toLRSHom.toShHom
    q.toLRSHom.toShHom c.toLRSHom.toShHom (congrArg (fun m : W ⟶ Z ↦ m.toLRSHom.toShHom) hb)
    (congrArg (fun m : V ⟶ Y ↦ m.toLRSHom.toShHom) hq)
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) hc)
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) hpb) K L φ

/-- The map on derived Hom induced by a factorisation of morphisms of schemes through an
identity is the identity. -/
theorem schemeFactorHom_id {f : X ⟶ X} (hf : f = 𝟙 X) (a : X ⟶ Z) (h : f ≫ a = a)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback a.toLRSHom.toShHom).obj K ⟶
      (derivedPullback a.toLRSHom.toShHom).obj L) :
    schemeFactorHom f a a h K L φ = φ :=
  factorHom_id (by subst hf; rfl) a.toLRSHom.toShHom
    (congrArg (fun m : X ⟶ Z ↦ m.toLRSHom.toShHom) h) K L φ

end Schemes

/-! ### Derived pullback around a commutative square of ringed spaces -/

section SquareRingedSpaces

variable {V V' W W' X Y Z : RingedSpace.{u, u}}

/-- The comparison isomorphism of a factorisation `f ≫ g = k` of morphisms of ringed spaces,
read as a bijection `Hom(Lf^*Lg^*K, Lf^*Lg^*L) ≃ Hom(Lk^*K, Lk^*L)` of derived morphism sets. -/
def factorEquiv (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    ((derivedPullback f).obj ((derivedPullback g).obj K) ⟶
        (derivedPullback f).obj ((derivedPullback g).obj L)) ≃
      ((derivedPullback k).obj K ⟶ (derivedPullback k).obj L) :=
  ((factorIso f g k h).app K).homCongr ((factorIso f g k h).app L)

/-- The map on derived Hom induced by a factorisation is the derived pullback along its first
factor, read through `factorEquiv`. -/
theorem factorHom_eq_factorEquiv (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (h : f ≫ g = k)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    factorHom f g k h K L φ = factorEquiv f g k h K L ((derivedPullback f).map φ) :=
  rfl

/-- For `c = p ≫ t ≫ a`, transporting the map induced by the inner factorisation `p ≫ t = q` along
the comparison isomorphism of `t ≫ a = b` gives the map induced by the outer factorisation
`p ≫ b = c`. -/
theorem factorEquiv_factorHom (p : V ⟶ W) (t : W ⟶ Y) (a : Y ⟶ Z) (b : W ⟶ Z) (q : V ⟶ Y)
    (c : V ⟶ Z) (hb : t ≫ a = b) (hq : p ≫ t = q) (hc : q ≫ a = c) (hpb : p ≫ b = c)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (ψ : (derivedPullback t).obj ((derivedPullback a).obj K) ⟶
      (derivedPullback t).obj ((derivedPullback a).obj L)) :
    factorEquiv q a c hc K L
        (factorHom p t q hq ((derivedPullback a).obj K) ((derivedPullback a).obj L) ψ) =
      factorHom p b c hpb K L (factorEquiv t a b hb K L ψ)  :=
  homCongr_factorIso_factorHom p t a b q c hb hq hc hpb K L ψ

/-- Derived pullback commutes with base change along a commutative square. For a commutative square
`r ≫ g = e ≫ ι` of morphisms of ringed spaces the two iterated derived pullbacks around it agree:
`Lι^* ⋙ Le^* ≅ Lg^* ⋙ Lr^*`. -/
def factorSquareIso (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z) (h : r ≫ g = e ≫ ι) :
    derivedPullback ι ⋙ derivedPullback e ≅ derivedPullback g ⋙ derivedPullback r :=
  factorIso e ι (e ≫ ι) rfl ≪≫ (factorIso r g (e ≫ ι) h).symm

/-- The map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Le^*Lι^*K, Le^*Lι^*L)` induced by a commutative square
`r ≫ g = e ≫ ι`: apply `Lr^*` and transport along `factorSquareIso`. -/
def factorSquareHom (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z) (h : r ≫ g = e ≫ ι)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    (derivedPullback e).obj ((derivedPullback ι).obj K) ⟶
      (derivedPullback e).obj ((derivedPullback ι).obj L) :=
  (factorEquiv e ι (e ≫ ι) rfl K L).symm (factorHom r g (e ≫ ι) h K L φ)

/-- The map on derived Hom of a commutative square is conjugation of the derived pullback along
its vertical edge by the square comparison isomorphism. -/
theorem factorSquareHom_eq (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z) (h : r ≫ g = e ≫ ι)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    factorSquareHom r g e ι h K L φ =
      (factorSquareIso r g e ι h).hom.app K ≫ (derivedPullback r).map φ ≫
        (factorSquareIso r g e ι h).inv.app L := by
  simp only [factorSquareHom, factorSquareIso, factorEquiv, factorHom, Iso.homCongr_symm,
    Iso.homCongr_apply, Iso.symm_hom, Iso.symm_inv, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Iso.app_hom, Iso.app_inv, Category.assoc]

/-- The square comparisons are compatible with factorisations of the horizontal edges. Two
commutative squares over `t ≫ g = g'` and under `s ≫ e = e'` whose vertical edges satisfy
`s ≫ r = r' ≫ t` induce maps on derived morphism sets that commute. -/
theorem factorHom_factorSquareHom (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z) (s : V' ⟶ V)
    (t : W' ⟶ W) (r' : V' ⟶ W') (g' : W' ⟶ Z) (e' : V' ⟶ Y) (h : r ≫ g = e ≫ ι)
    (h' : r' ≫ g' = e' ≫ ι) (hse : s ≫ e = e') (ht : t ≫ g = g') (hsr : s ≫ r = r' ≫ t)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj K ⟶ (derivedPullback g).obj L) :
    factorHom s e e' hse ((derivedPullback ι).obj K) ((derivedPullback ι).obj L)
        (factorSquareHom r g e ι h K L φ) =
      factorSquareHom r' g' e' ι h' K L (factorHom t g g' ht K L φ) := by
  have hpb : s ≫ e ≫ ι = e' ≫ ι := by rw [← Category.assoc, hse]
  have hc : (r' ≫ t) ≫ g = e' ≫ ι := by rw [Category.assoc, ht, h']
  apply (factorEquiv e' ι (e' ≫ ι) rfl K L).injective
  simp only [factorSquareHom]
  rw [factorEquiv_factorHom s e ι (e ≫ ι) e' (e' ≫ ι) rfl hse rfl hpb K L,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    factorHom_comp s r g (e ≫ ι) (r' ≫ t) (e' ≫ ι) h hsr hc hpb K L φ,
    factorHom_comp r' t g g' (r' ≫ t) (e' ≫ ι) ht rfl hc h' K L φ]

end SquareRingedSpaces

/-! ### Derived pullback around a commutative square of schemes -/

section SquareSchemes

variable {V V' W W' Y Z : Scheme.{u}}

/-- Derived pullback commutes with base change along a commutative square of schemes. For a
commutative square `r ≫ g = e ≫ ι` the two iterated derived pullbacks around it agree:
`Lι^* ⋙ Le^* ≅ Lg^* ⋙ Lr^*`. -/
def schemeFactorSquareIso (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z)
    (h : r ≫ g = e ≫ ι) :
    derivedPullback ι.toLRSHom.toShHom ⋙ derivedPullback e.toLRSHom.toShHom ≅
      derivedPullback g.toLRSHom.toShHom ⋙ derivedPullback r.toLRSHom.toShHom :=
  factorSquareIso r.toLRSHom.toShHom g.toLRSHom.toShHom e.toLRSHom.toShHom ι.toLRSHom.toShHom
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) h)

/-- The map `Hom(Lg^*K, Lg^*L) ⟶ Hom(Le^*Lι^*K, Le^*Lι^*L)` induced by a commutative square
`r ≫ g = e ≫ ι` of morphisms of schemes. -/
def schemeFactorSquareHom (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z) (h : r ≫ g = e ≫ ι)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    (derivedPullback e.toLRSHom.toShHom).obj ((derivedPullback ι.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback e.toLRSHom.toShHom).obj ((derivedPullback ι.toLRSHom.toShHom).obj L) :=
  factorSquareHom r.toLRSHom.toShHom g.toLRSHom.toShHom e.toLRSHom.toShHom ι.toLRSHom.toShHom
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) h) K L φ

/-- The map on derived Hom of a commutative square of schemes is conjugation of the derived
pullback along its vertical edge by the square comparison isomorphism. -/
theorem schemeFactorSquareHom_eq (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z)
    (h : r ≫ g = e ≫ ι)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    schemeFactorSquareHom r g e ι h K L φ =
      (schemeFactorSquareIso r g e ι h).hom.app K ≫
        (derivedPullback r.toLRSHom.toShHom).map φ ≫ (schemeFactorSquareIso r g e ι h).inv.app L :=
  factorSquareHom_eq r.toLRSHom.toShHom g.toLRSHom.toShHom e.toLRSHom.toShHom ι.toLRSHom.toShHom
    (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) h) K L φ

/-- The square comparisons of schemes are compatible with factorisations of the horizontal edges.
Two commutative squares over `t ≫ g = g'` and under `s ≫ e = e'` whose vertical edges satisfy
`s ≫ r = r' ≫ t` induce maps on derived morphism sets that commute. -/
theorem schemeFactorHom_schemeFactorSquareHom (r : V ⟶ W) (g : W ⟶ Z) (e : V ⟶ Y) (ι : Y ⟶ Z)
    (s : V' ⟶ V) (t : W' ⟶ W) (r' : V' ⟶ W') (g' : W' ⟶ Z) (e' : V' ⟶ Y) (h : r ≫ g = e ≫ ι)
    (h' : r' ≫ g' = e' ≫ ι) (hse : s ≫ e = e') (ht : t ≫ g = g') (hsr : s ≫ r = r' ≫ t)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g.toLRSHom.toShHom).obj L) :
    schemeFactorHom s e e' hse ((derivedPullback ι.toLRSHom.toShHom).obj K)
        ((derivedPullback ι.toLRSHom.toShHom).obj L) (schemeFactorSquareHom r g e ι h K L φ) =
      schemeFactorSquareHom r' g' e' ι h' K L (schemeFactorHom t g g' ht K L φ) :=
  factorHom_factorSquareHom r.toLRSHom.toShHom g.toLRSHom.toShHom e.toLRSHom.toShHom
    ι.toLRSHom.toShHom s.toLRSHom.toShHom t.toLRSHom.toShHom r'.toLRSHom.toShHom
    g'.toLRSHom.toShHom e'.toLRSHom.toShHom (congrArg (fun m : V ⟶ Z ↦ m.toLRSHom.toShHom) h)
    (congrArg (fun m : V' ⟶ Z ↦ m.toLRSHom.toShHom) h')
    (congrArg (fun m : V' ⟶ Y ↦ m.toLRSHom.toShHom) hse)
    (congrArg (fun m : W' ⟶ Z ↦ m.toLRSHom.toShHom) ht)
    (congrArg (fun m : V' ⟶ W ↦ m.toLRSHom.toShHom) hsr) K L φ

end SquareSchemes

end Stacks.DerivedPullback

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)

/-! ### Factorisations of the transition and projection morphisms -/

/-- The transition morphism to a later stage lies over `X₀`: `f_{ji} ≫ f_{i0} = f_{j0}`. -/
theorem transition_comp_toFixedStage {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.transition h ≫ D.toFixedStage i = D.toFixedStage j :=
  pullback.lift_fst _ _ _

/-- The projection from the limit lies over `X₀`: `fᵢ ≫ f_{i0} = f₀`. -/
theorem projection_comp_toFixedStage (i : D.LaterIndex) :
    D.projection i ≫ D.toFixedStage i = D.limitToFixedStage :=
  pullback.lift_fst _ _ _

/-- The transition morphism from a stage to itself is the identity. -/
theorem transition_refl (i : D.LaterIndex) :
    D.transition (le_refl i.1) = 𝟙 (D.schemeAt i) := by
  apply pullback.hom_ext <;> simp [transition]

/-- The transition morphisms compose: `f_{kj} ≫ f_{ji} = f_{ki}`. -/
theorem transition_comp_transition {i j k : D.LaterIndex} (hij : i.1 ≤ j.1) (hjk : j.1 ≤ k.1) :
    D.transition hjk ≫ D.transition hij = D.transition (hij.trans hjk) := by
  apply pullback.hom_ext
  · simp only [transition, Category.assoc, pullback.lift_fst]
  · simp only [transition, pullback.lift_snd, pullback.lift_snd_assoc, Category.assoc,
      ← Functor.map_comp]
    exact congrArg (fun m ↦ pullback.snd D.X₀.hom (D.baseMap k) ≫ D.descent.system.map m)
      (Subsingleton.elim _ _)

/-- The projections from the limit are compatible with the transition morphisms:
`fⱼ ≫ f_{ji} = fᵢ`. -/
theorem projection_comp_transition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    D.projection j ≫ D.transition h = D.projection i := by
  apply pullback.hom_ext
  · simp only [transition, projection, Category.assoc, pullback.lift_fst]
  · simp only [transition, projection, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
    exact congrArg (fun m ↦ pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base))
      ≫ m) (D.descent.limitCone.w (homOfLE h).op)

/-- The fixed stage is a stage at or beyond itself. -/
theorem nonempty_laterIndex : Nonempty D.LaterIndex :=
  ⟨⟨D.descent.base, le_refl _⟩⟩

/-- The stages at or beyond the fixed stage are directed. -/
theorem isDirected_laterIndex : IsDirected D.LaterIndex (· ≤ ·) := by
  constructor
  intro i j
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.1 j.1
  exact ⟨⟨k, i.2.trans hik⟩, hik, hjk⟩

/-! ### The system of derived morphism sets -/

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))

/-- The transition map from `Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀)` to
`Hom_{D(𝒪_{Xⱼ})}(Lf_{j0}^*K₀, Lf_{j0}^*L₀)` for `i ≤ j`, given by applying `Lf_{ji}^*`. -/
def homTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    (derivedPullback (D.toFixedStage j).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage j).toLRSHom.toShHom).obj L₀ :=
  Stacks.DerivedPullback.schemeFactorHom (D.transition h) (D.toFixedStage i) (D.toFixedStage j)
    (D.transition_comp_toFixedStage h) K₀ L₀ φ

/-- The comparison map from `Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀)` to
`Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)`, given by applying `Lfᵢ^*`. -/
def homComparison (i : D.LaterIndex)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj L₀ :=
  Stacks.DerivedPullback.schemeFactorHom (D.projection i) (D.toFixedStage i) D.limitToFixedStage
    (D.projection_comp_toFixedStage i) K₀ L₀ φ

/-- The transition map of the system of derived morphism sets at a stage to itself is the
identity. -/
theorem homTransition_refl (i : D.LaterIndex) :
    D.homTransition K₀ L₀ (le_refl i.1) = id :=
  funext fun φ ↦ Stacks.DerivedPullback.schemeFactorHom_id (D.transition_refl i)
    (D.toFixedStage i) (D.transition_comp_toFixedStage (le_refl i.1)) K₀ L₀ φ

/-- The transition maps of the system of derived morphism sets compose. -/
theorem homTransition_homTransition {i j k : D.LaterIndex} (hij : i.1 ≤ j.1) (hjk : j.1 ≤ k.1)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    D.homTransition K₀ L₀ hjk (D.homTransition K₀ L₀ hij φ) =
      D.homTransition K₀ L₀ (hij.trans hjk) φ :=
  Stacks.DerivedPullback.schemeFactorHom_comp (D.transition hjk) (D.transition hij)
    (D.toFixedStage i) (D.toFixedStage j) (D.transition (hij.trans hjk)) (D.toFixedStage k)
    (D.transition_comp_toFixedStage hij) (D.transition_comp_transition hij hjk)
    (D.transition_comp_toFixedStage (hij.trans hjk)) (D.transition_comp_toFixedStage hjk)
    K₀ L₀ φ

/-- The comparison maps of the system of derived morphism sets are compatible with its transition
maps, so they define a map out of the colimit over the stages. -/
theorem homComparison_homTransition {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    D.homComparison K₀ L₀ j (D.homTransition K₀ L₀ h φ) = D.homComparison K₀ L₀ i φ :=
  Stacks.DerivedPullback.schemeFactorHom_comp (D.projection j) (D.transition h)
    (D.toFixedStage i) (D.toFixedStage j) (D.projection i) D.limitToFixedStage
    (D.transition_comp_toFixedStage h) (D.projection_comp_transition h)
    (D.projection_comp_toFixedStage i) (D.projection_comp_toFixedStage j) K₀ L₀ φ

/-- Descent for derived morphism sets: every morphism `Lf₀^*K₀ ⟶ Lf₀^*L₀` is the comparison of a
morphism at some stage, and two morphisms at a stage with the same comparison agree at some later
stage. Equivalently `colim_i Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ) ⟶ Hom_{D(𝒪_X)}(K, L)` is bijective. -/
def HomDescent : Prop :=
  (∀ ψ : (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj K₀ ⟶
        (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj L₀,
      ∃ (i : D.LaterIndex)
        (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
          (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀),
        D.homComparison K₀ L₀ i φ = ψ) ∧
    ∀ (i : D.LaterIndex)
      (φ φ' : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
        (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀),
      D.homComparison K₀ L₀ i φ = D.homComparison K₀ L₀ i φ' →
        ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1),
          D.homTransition K₀ L₀ h φ = D.homTransition K₀ L₀ h φ'

/-! ### The system of derived morphism sets as a functor -/

/-- The system `i ↦ Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀)` of derived morphism sets over the
stages at or beyond the fixed stage, with transition maps `homTransition`. -/
def homFunctor : D.LaterIndex ⥤ Type (u + 1) where
  obj i := (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
    (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀
  map h := TypeCat.ofHom (D.homTransition K₀ L₀ (leOfHom h))
  map_id i := by
    ext φ
    exact congrFun (D.homTransition_refl K₀ L₀ i) φ
  map_comp f g := by
    ext φ
    exact (D.homTransition_homTransition K₀ L₀ (leOfHom f) (leOfHom g) φ).symm

/-- The cocone on `homFunctor` with vertex `Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)` whose leg at a stage
is the comparison map `homComparison`. -/
def homCocone : Cocone (D.homFunctor K₀ L₀) where
  pt := (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj K₀ ⟶
    (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj L₀
  ι :=
    { app i := TypeCat.ofHom (D.homComparison K₀ L₀ i)
      naturality := fun i j h ↦ by
        ext φ
        exact D.homComparison_homTransition K₀ L₀ (leOfHom h) φ }

/-- `HomDescent` holds exactly when the comparison maps exhibit `Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀)` as
the colimit of the system of derived morphism sets over the stages at or beyond the fixed stage. -/
theorem homDescent_iff_nonempty_isColimit :
    D.HomDescent K₀ L₀ ↔ Nonempty (IsColimit (D.homCocone K₀ L₀)) := by
  have _ : Nonempty D.LaterIndex := D.nonempty_laterIndex
  have _ : IsDirected D.LaterIndex (· ≤ ·) := D.isDirected_laterIndex
  constructor
  · rintro ⟨hsurj, hinj⟩
    refine ⟨Types.FilteredColimit.isColimitOf' _ _ ?_ ?_⟩
    · intro ψ
      obtain ⟨i, φ, hφ⟩ := hsurj ψ
      exact ⟨i, φ, hφ.symm⟩
    · intro i φ φ' hφ
      obtain ⟨j, hij, hj⟩ := hinj i φ φ' hφ
      exact ⟨j, homOfLE hij, hj⟩
  · rintro ⟨hc⟩
    refine ⟨fun ψ ↦ ?_, fun i φ φ' hφ ↦ ?_⟩
    · obtain ⟨i, φ, hφ⟩ := Types.jointly_surjective_of_isColimit hc ψ
      exact ⟨i, φ, hφ⟩
    · obtain ⟨j, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc φ φ').1 hφ
      exact ⟨j, leOfHom f, hf⟩

/-! ### Restriction to a quasi-compact open of the fixed stage -/

/-- The relative descent situation restricted to a quasi-compact open `U₀ ⊆ X₀`. The inverse system
and its limit are unchanged, and `U₀ ⟶ S₀` is again flat of finite presentation. -/
def restrict (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left)) :
    RelativeDescentSituation.{v, u} I where
  descent := D.descent
  X₀ := Over.mk (U₀.ι ≫ D.X₀.hom)
  flat := by
    have := D.flat
    exact (inferInstance : Flat (U₀.ι ≫ D.X₀.hom))
  finitePresentation := by
    have := D.finitePresentation.locallyOfFinitePresentation
    have := D.finitePresentation.quasiSeparated
    have : QuasiSeparatedSpace (D.descent.system.obj (op D.descent.base)) :=
      D.descent.quasiSeparated D.descent.base
    have : CompactSpace U₀.toScheme := isCompact_iff_compactSpace.mp hU₀
    exact ⟨(inferInstance : LocallyOfFinitePresentation (U₀.ι ≫ D.X₀.hom)),
      (inferInstance : QuasiCompact (U₀.ι ≫ D.X₀.hom)),
      (inferInstance : QuasiSeparated (U₀.ι ≫ D.X₀.hom))⟩

attribute [local implicit_reducible] restrict

variable (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))

/-- The restricted situation has the same inverse system, limit and fixed stage, hence the same
stages at or beyond it. -/
theorem restrict_descent : (D.restrict U₀ hU₀).descent = D.descent :=
  rfl

/-- The scheme over the fixed stage of the restricted situation is `U₀`. -/
theorem restrict_X₀_left : (D.restrict U₀ hU₀).X₀.left = U₀.toScheme :=
  rfl

/-- The structure morphism of the restricted situation is `U₀ ⟶ X₀ ⟶ S₀`. -/
theorem restrict_X₀_hom : (D.restrict U₀ hU₀).X₀.hom = U₀.ι ≫ D.X₀.hom :=
  rfl

/-- The canonical morphism `Uᵢ = Sᵢ ×_{S₀} U₀ ⟶ Xᵢ = Sᵢ ×_{S₀} X₀`, the base change of the
inclusion `U₀ ⟶ X₀` along `f_{i0}`. -/
def restrictToAmbient (i : D.LaterIndex) :
    (D.restrict U₀ hU₀).schemeAt i ⟶ D.schemeAt i :=
  (pullbackRightPullbackFstIso D.X₀.hom (D.baseMap i) U₀.ι).inv ≫
    pullback.snd U₀.ι (D.toFixedStage i)

/-- The stage of the restricted situation is an open subscheme of the corresponding stage. -/
instance isOpenImmersion_restrictToAmbient (i : D.LaterIndex) :
    IsOpenImmersion (D.restrictToAmbient U₀ hU₀ i) := by
  change IsOpenImmersion ((pullbackRightPullbackFstIso D.X₀.hom (D.baseMap i) U₀.ι).inv ≫
    pullback.snd U₀.ι (D.toFixedStage i))
  infer_instance

/-- The inclusion `Uᵢ ⟶ Xᵢ` lies over the inclusion `U₀ ⟶ X₀`. -/
theorem restrictToAmbient_comp_toFixedStage (i : D.LaterIndex) :
    D.restrictToAmbient U₀ hU₀ i ≫ D.toFixedStage i =
      (D.restrict U₀ hU₀).toFixedStage i ≫ U₀.ι :=
  (Category.assoc _ _ _).trans
    (pullbackRightPullbackFstIso_inv_snd_fst D.X₀.hom (D.baseMap i) U₀.ι)

/-- The inclusion `Uᵢ ⟶ Xᵢ` is a morphism over `Sᵢ`. -/
theorem restrictToAmbient_comp_snd (i : D.LaterIndex) :
    D.restrictToAmbient U₀ hU₀ i ≫ pullback.snd D.X₀.hom (D.baseMap i) =
      pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) :=
  (Category.assoc _ _ _).trans
    (pullbackRightPullbackFstIso_inv_snd_snd D.X₀.hom (D.baseMap i) U₀.ι)

/-- The base change of an open inclusion `U ⟶ X` along `pullback.fst f g` has range the preimage
of `U`. -/
private theorem opensRange_pullbackRightPullbackFstIso_inv_comp_snd {S X Y : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (U : X.Opens) :
    ((pullbackRightPullbackFstIso f g U.ι).inv ≫ pullback.snd U.ι (pullback.fst f g)).opensRange =
      pullback.fst f g ⁻¹ᵁ U := by
  have h := Scheme.Hom.opensRange_comp_of_isIso (pullbackRightPullbackFstIso f g U.ι).inv
    (pullback.snd U.ι (pullback.fst f g))
  rwa [Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι] at h

/-- The stage of the restricted situation is the preimage of `U₀` in `Xᵢ`. -/
theorem opensRange_restrictToAmbient (i : D.LaterIndex) :
    (D.restrictToAmbient U₀ hU₀ i).opensRange = D.toFixedStage i ⁻¹ᵁ U₀ :=
  opensRange_pullbackRightPullbackFstIso_inv_comp_snd D.X₀.hom (D.baseMap i) U₀

/-- The canonical morphism `U = S ×_{S₀} U₀ ⟶ X = S ×_{S₀} X₀`, the base change of the inclusion
`U₀ ⟶ X₀` along `f₀`. -/
def restrictToAmbientLimit : (D.restrict U₀ hU₀).limitScheme ⟶ D.limitScheme :=
  (pullbackRightPullbackFstIso D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) U₀.ι).inv ≫
    pullback.snd U₀.ι D.limitToFixedStage

/-- The limit of the restricted situation is an open subscheme of the limit. -/
instance isOpenImmersion_restrictToAmbientLimit :
    IsOpenImmersion (D.restrictToAmbientLimit U₀ hU₀) := by
  change IsOpenImmersion ((pullbackRightPullbackFstIso D.X₀.hom
      (D.descent.limitCone.π.app (op D.descent.base)) U₀.ι).inv ≫
    pullback.snd U₀.ι D.limitToFixedStage)
  infer_instance

/-- The inclusion `U ⟶ X` lies over the inclusion `U₀ ⟶ X₀`. -/
theorem restrictToAmbientLimit_comp_limitToFixedStage :
    D.restrictToAmbientLimit U₀ hU₀ ≫ D.limitToFixedStage =
      (D.restrict U₀ hU₀).limitToFixedStage ≫ U₀.ι :=
  (Category.assoc _ _ _).trans (pullbackRightPullbackFstIso_inv_snd_fst D.X₀.hom
    (D.descent.limitCone.π.app (op D.descent.base)) U₀.ι)

/-- The inclusion `U ⟶ X` is a morphism over `S`. -/
theorem restrictToAmbientLimit_comp_snd :
    D.restrictToAmbientLimit U₀ hU₀ ≫
        pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) =
      pullback.snd (U₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)) :=
  (Category.assoc _ _ _).trans (pullbackRightPullbackFstIso_inv_snd_snd D.X₀.hom
    (D.descent.limitCone.π.app (op D.descent.base)) U₀.ι)

/-- The limit of the restricted situation is the preimage of `U₀` in `X`. -/
theorem opensRange_restrictToAmbientLimit :
    (D.restrictToAmbientLimit U₀ hU₀).opensRange = D.limitToFixedStage ⁻¹ᵁ U₀ :=
  opensRange_pullbackRightPullbackFstIso_inv_comp_snd D.X₀.hom
    (D.descent.limitCone.π.app (op D.descent.base)) U₀

/-- The inclusions `Uᵢ ⟶ Xᵢ` are compatible with the transition morphisms. -/
theorem restrictToAmbient_transition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (D.restrict U₀ hU₀).transition h ≫ D.restrictToAmbient U₀ hU₀ i =
      D.restrictToAmbient U₀ hU₀ j ≫ D.transition h := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i, ← Category.assoc,
      (D.restrict U₀ hU₀).transition_comp_toFixedStage h, Category.assoc,
      D.transition_comp_toFixedStage h, D.restrictToAmbient_comp_toFixedStage U₀ hU₀ j]
  · rw [Category.assoc, D.restrictToAmbient_comp_snd U₀ hU₀ i, Category.assoc,
      show D.transition h ≫ pullback.snd D.X₀.hom (D.baseMap i) =
          pullback.snd D.X₀.hom (D.baseMap j) ≫ D.descent.system.map (homOfLE h).op from
        pullback.lift_snd _ _ _,
      ← Category.assoc, D.restrictToAmbient_comp_snd U₀ hU₀ j]
    exact pullback.lift_snd _ _ _

/-- The inclusions `Uᵢ ⟶ Xᵢ` and `U ⟶ X` are compatible with the projections from the limit. -/
theorem restrictToAmbient_projection (i : D.LaterIndex) :
    (D.restrict U₀ hU₀).projection i ≫ D.restrictToAmbient U₀ hU₀ i =
      D.restrictToAmbientLimit U₀ hU₀ ≫ D.projection i := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i, ← Category.assoc,
      (D.restrict U₀ hU₀).projection_comp_toFixedStage i, Category.assoc,
      D.projection_comp_toFixedStage i,
      D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀]
  · rw [Category.assoc, D.restrictToAmbient_comp_snd U₀ hU₀ i, Category.assoc,
      show D.projection i ≫ pullback.snd D.X₀.hom (D.baseMap i) =
          pullback.snd D.X₀.hom (D.descent.limitCone.π.app (op D.descent.base)) ≫
            D.descent.limitCone.π.app (op i.1) from pullback.lift_snd _ _ _,
      ← Category.assoc, D.restrictToAmbientLimit_comp_snd U₀ hU₀]
    exact pullback.lift_snd _ _ _

/-! ### Base change of the derived pullbacks of the restricted situation -/

/-- The derived pullback to a stage commutes with restriction to a quasi-compact open. The derived
pullback along `f_{i0} : Uᵢ ⟶ U₀` of the restriction to `U₀` of an object of `D(𝒪_{X₀})` is its
derived pullback along `f_{i0} : Xᵢ ⟶ X₀` restricted to `Uᵢ`. -/
def restrictDerivedPullbackIso (i : D.LaterIndex) :
    derivedPullback U₀.ι.toLRSHom.toShHom ⋙
        derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom ≅
      derivedPullback (D.toFixedStage i).toLRSHom.toShHom ⋙
        derivedPullback (D.restrictToAmbient U₀ hU₀ i).toLRSHom.toShHom :=
  Stacks.DerivedPullback.schemeFactorSquareIso (D.restrictToAmbient U₀ hU₀ i) (D.toFixedStage i)
    ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i)

/-- The derived pullback to the limit commutes with restriction to a quasi-compact open. The
derived pullback along `f₀ : U ⟶ U₀` of the restriction to `U₀` of an object of `D(𝒪_{X₀})` is its
derived pullback along `f₀ : X ⟶ X₀` restricted to `U`. -/
def restrictDerivedPullbackLimitIso :
    derivedPullback U₀.ι.toLRSHom.toShHom ⋙
        derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom ≅
      derivedPullback D.limitToFixedStage.toLRSHom.toShHom ⋙
        derivedPullback (D.restrictToAmbientLimit U₀ hU₀).toLRSHom.toShHom :=
  Stacks.DerivedPullback.schemeFactorSquareIso (D.restrictToAmbientLimit U₀ hU₀)
    D.limitToFixedStage (D.restrict U₀ hU₀).limitToFixedStage U₀.ι
    (D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀)

/-- Restriction to `Uᵢ` on derived morphism sets, from `Hom_{D(𝒪_{Xᵢ})}(Lf_{i0}^*K₀, Lf_{i0}^*L₀)`
to `Hom_{D(𝒪_{Uᵢ})}(Lf_{i0}^*(K₀|_{U₀}), Lf_{i0}^*(L₀|_{U₀}))`: apply the derived pullback along
`Uᵢ ⟶ Xᵢ` and transport along `restrictDerivedPullbackIso`. -/
def homRestrictToOpen (i : D.LaterIndex)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
      (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) :=
  Stacks.DerivedPullback.schemeFactorSquareHom (D.restrictToAmbient U₀ hU₀ i) (D.toFixedStage i)
    ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i)
    K₀ L₀ φ

/-- Restriction to `U` on derived morphism sets,
`Hom_{D(𝒪_X)}(Lf₀^*K₀, Lf₀^*L₀) ⟶ Hom_{D(𝒪_U)}(Lf₀^*(K₀|_{U₀}), Lf₀^*(L₀|_{U₀}))`: apply the
derived pullback along `U ⟶ X` and transport along `restrictDerivedPullbackLimitIso`. -/
def homRestrictToOpenLimit
    (φ : (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj L₀) :
    (derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom).obj
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
      (derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom).obj
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) :=
  Stacks.DerivedPullback.schemeFactorSquareHom (D.restrictToAmbientLimit U₀ hU₀)
    D.limitToFixedStage (D.restrict U₀ hU₀).limitToFixedStage U₀.ι
    (D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀) K₀ L₀ φ

/-- Restriction to `U₀` is a map of systems of derived morphism sets. It commutes with the
transition maps of the ambient situation and of the restricted one. -/
theorem homTransition_homRestrictToOpen {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    (D.restrict U₀ hU₀).homTransition ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) h
        (D.homRestrictToOpen K₀ L₀ U₀ hU₀ i φ) =
      D.homRestrictToOpen K₀ L₀ U₀ hU₀ j (D.homTransition K₀ L₀ h φ) :=
  Stacks.DerivedPullback.schemeFactorHom_schemeFactorSquareHom (D.restrictToAmbient U₀ hU₀ i)
    (D.toFixedStage i) ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
    ((D.restrict U₀ hU₀).transition h) (D.transition h) (D.restrictToAmbient U₀ hU₀ j)
    (D.toFixedStage j) ((D.restrict U₀ hU₀).toFixedStage j)
    (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i)
    (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ j)
    ((D.restrict U₀ hU₀).transition_comp_toFixedStage h) (D.transition_comp_toFixedStage h)
    (D.restrictToAmbient_transition U₀ hU₀ h) K₀ L₀ φ

/-- Restriction to `U₀` is a map of cocones on the systems of derived morphism sets. It commutes
with the comparison maps to the limit of the ambient situation and of the restricted one. -/
theorem homComparison_homRestrictToOpen (i : D.LaterIndex)
    (φ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    (D.restrict U₀ hU₀).homComparison ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) i
        (D.homRestrictToOpen K₀ L₀ U₀ hU₀ i φ) =
      D.homRestrictToOpenLimit K₀ L₀ U₀ hU₀ (D.homComparison K₀ L₀ i φ) :=
  Stacks.DerivedPullback.schemeFactorHom_schemeFactorSquareHom (D.restrictToAmbient U₀ hU₀ i)
    (D.toFixedStage i) ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
    ((D.restrict U₀ hU₀).projection i) (D.projection i) (D.restrictToAmbientLimit U₀ hU₀)
    D.limitToFixedStage (D.restrict U₀ hU₀).limitToFixedStage
    (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i)
    (D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀)
    ((D.restrict U₀ hU₀).projection_comp_toFixedStage i) (D.projection_comp_toFixedStage i)
    (D.restrictToAmbient_projection U₀ hU₀ i) K₀ L₀ φ

/-- Restriction to `U₀` as a morphism of the systems of derived morphism sets over the stages at
or beyond the fixed stage. -/
def homFunctorRestrictToOpen :
    D.homFunctor K₀ L₀ ⟶ (D.restrict U₀ hU₀).homFunctor
      ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
      ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) where
  app i := TypeCat.ofHom (D.homRestrictToOpen K₀ L₀ U₀ hU₀ i)
  naturality i j h := by
    ext φ
    exact (D.homTransition_homRestrictToOpen K₀ L₀ U₀ hU₀ (leOfHom h) φ).symm

/-- `HomDescent` for the restriction to a quasi-compact open `U₀ ⊆ X₀`, as a predicate on `U₀`: the
morphism sets between the derived pullbacks of `K₀|_{U₀}` and `L₀|_{U₀}` over the stages at or
beyond the fixed stage have colimit the morphism set over `U`. -/
def RestrictHomDescent : Prop :=
  (D.restrict U₀ hU₀).HomDescent ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
    ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)

/-- `RestrictHomDescent` holds exactly when the comparison maps exhibit
`Hom_{D(𝒪_U)}(Lf₀^*(K₀|_{U₀}), Lf₀^*(L₀|_{U₀}))` as the colimit of the system of derived
morphism sets of the restricted situation. -/
theorem restrictHomDescent_iff_nonempty_isColimit :
    D.RestrictHomDescent K₀ L₀ U₀ hU₀ ↔
      Nonempty (IsColimit ((D.restrict U₀ hU₀).homCocone
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀))) :=
  (D.restrict U₀ hU₀).homDescent_iff_nonempty_isColimit _ _

end AlgebraicGeometry.RelativeDescentSituation

end
