module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ThickeningPushoutFlatInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# Gluing two compatible quotients over a pushout along a thickening

In the situation of Stacks 08IW, let `a : V ⟶ P`, `b : U' ⟶ P`, `c : U ⟶ V` and `d : U ⟶ U'` be
the base changes of the pushout square along `X → B`, over a common `sP : P ⟶ X₀`. Two quotients
`πA : sV^*F ⟶ A` and `πB : sU'^*F ⟶ B'`, identified over `U` by `θ : d^*B' ⟶ c^*A`, give two maps
from `sP^*F` to `(c ≫ a)_*c^*A`, the adjoints of the projections followed by the units; we show
that they agree (`glueLift_compat`), so that they define a map from `sP^*F` into the glued module
of Stacks 08KV. The coherence is proved abstractly for squares of adjunctions
(`CategoryTheory.square_coherence`, `CategoryTheory.square_homEquiv_compat`).

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace CategoryTheory

/-- **An abstract coherence around a commutative square of inverse images.**  The objects and
isomorphisms are those of the inverse images along the sides of a square `c ≫ a = d ≫ b` over a
common `sP`; the hypotheses are the associativity coherences of the comparisons and the
identification of the two composites. -/
theorem square_coherence {C₀ CP CV CU' CU : Type*} [Category* C₀] [Category* CP] [Category* CV]
    [Category* CU'] [Category* CU]
    {sP : C₀ ⥤ CP} {sV : C₀ ⥤ CV} {sU' : C₀ ⥤ CU'} {sU : C₀ ⥤ CU} {a : CP ⥤ CV}
    {b : CP ⥤ CU'} {c : CV ⥤ CU} {d : CU' ⥤ CU} {ca db : CP ⥤ CU}
    (Ea : sV ≅ sP ⋙ a) (Eb : sU' ≅ sP ⋙ b) (Ec : sU ≅ sV ⋙ c) (Ed : sU ≅ sU' ⋙ d)
    (Tca : ca ≅ a ⋙ c) (Tdb : db ≅ b ⋙ d) (Kca : sU ≅ sP ⋙ ca) (Kdb : sU ≅ sP ⋙ db)
    (hL : ca = db) (hL' : db = ca) (F : C₀) {A : CV} {B' : CU'} (πA : sV.obj F ⟶ A)
    (πB : sU'.obj F ⟶ B') (θ : d.obj B' ⟶ c.obj A)
    (G₁ : c.map (Ea.inv.app F) ≫ Ec.inv.app F = Tca.inv.app (sP.obj F) ≫ Kca.inv.app F)
    (G₂ : d.map (Eb.inv.app F) ≫ Ed.inv.app F = Tdb.inv.app (sP.obj F) ≫ Kdb.inv.app F)
    (G₃ : Kca = Kdb ≪≫ Functor.isoWhiskerLeft sP (eqToIso hL'))
    (hθ : Ed.hom.app F ≫ d.map πB ≫ θ = Ec.hom.app F ≫ c.map πA) :
    Tca.hom.app (sP.obj F) ≫ c.map (Ea.inv.app F ≫ πA) =
      (eqToHom hL).app (sP.obj F) ≫ (Tdb.hom.app (sP.obj F) ≫ d.map (Eb.inv.app F ≫ πB)) ≫ θ := by
  subst hL
  simp only [eqToIso_refl, Functor.isoWhiskerLeft_refl, Iso.trans_refl] at G₃
  subst G₃
  have e₁ : c.map (Ea.inv.app F) = (Tca.inv.app (sP.obj F) ≫ Kca.inv.app F) ≫ Ec.hom.app F := by
    rw [← G₁, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  have e₂ : d.map (Eb.inv.app F) = (Tdb.inv.app (sP.obj F) ≫ Kca.inv.app F) ≫ Ed.hom.app F := by
    rw [← G₂, Category.assoc, Iso.inv_hom_id_app]
    exact (Category.comp_id _).symm
  simp only [Functor.map_comp, e₁, e₂, eqToHom_refl, NatTrans.id_app, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc, hθ]

/-- **An abstract compatibility of two transposes along a commutative square of adjunctions.** -/
theorem square_homEquiv_compat {CP CV CU' CU : Type*} [Category* CP] [Category* CV]
    [Category* CU'] [Category* CU]
    {a : CP ⥤ CV} {a' : CV ⥤ CP} {b : CP ⥤ CU'} {b' : CU' ⥤ CP} {c : CV ⥤ CU} {c' : CU ⥤ CV}
    {d : CU' ⥤ CU} {d' : CU ⥤ CU'} {ca : CP ⥤ CU} {ca' : CU ⥤ CP} {db : CP ⥤ CU}
    {db' : CU ⥤ CP} (adjA : a ⊣ a') (adjB : b ⊣ b') (adjC : c ⊣ c') (adjD : d ⊣ d')
    (adjCA : ca ⊣ ca') (adjDB : db ⊣ db') (pca : c' ⋙ a' ≅ ca') (pdb : d' ⋙ b' ≅ db')
    (qca : a ⋙ c ≅ ca) (qdb : b ⋙ d ≅ db) (e : db' ⟶ ca') (e' : ca ⟶ db)
    (Hca : ∀ (M : CP) (A' : CV) (u : a.obj M ⟶ A'),
      adjA.homEquiv M A' u ≫ a'.map (adjC.unit.app A') ≫ pca.hom.app (c.obj A') =
        adjCA.homEquiv M (c.obj A') (qca.inv.app M ≫ c.map u))
    (Hdb : ∀ (M : CP) (A' : CU') (u : b.obj M ⟶ A'),
      adjB.homEquiv M A' u ≫ b'.map (adjD.unit.app A') ≫ pdb.hom.app (d.obj A') =
        adjDB.homEquiv M (d.obj A') (qdb.inv.app M ≫ d.map u))
    (Ht : ∀ (N : CP) (M : CU) (w : db.obj N ⟶ M),
      adjDB.homEquiv N M w ≫ e.app M = adjCA.homEquiv N M (e'.app N ≫ w))
    (N : CP) {A : CV} {B' : CU'} (u : a.obj N ⟶ A) (v : b.obj N ⟶ B') (θ : d.obj B' ⟶ c.obj A)
    (ηc : A ⟶ c'.obj (c.obj A)) (ηd : B' ⟶ d'.obj (d.obj B'))
    (hηc : ηc = adjC.unit.app A) (hηd : ηd = adjD.unit.app B') (e'' : ca ⟶ db) (he : e' = e'')
    (Co : qca.inv.app N ≫ c.map u = e''.app N ≫ (qdb.inv.app N ≫ d.map v) ≫ θ) :
    adjA.homEquiv N A u ≫ (a'.map ηc ≫ pca.hom.app (c.obj A)) =
      adjB.homEquiv N B' v ≫ ((b'.map ηd ≫ pdb.hom.app (d.obj B')) ≫ e.app (d.obj B') ≫
        ca'.map θ) := by
  subst hηc hηd he
  rw [Hca, Co, ← Category.assoc, Adjunction.homEquiv_naturality_right, ← Ht, ← Hdb,
    Category.assoc, Category.assoc, Category.assoc]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The transpose along a composite of morphisms of algebraic spaces, transported along an equality
of two composites. -/
theorem homEquiv_comp_eqToHom_modulePushforward {X Y Y' Z : AlgebraicSpaces B S hS}
    {f₁ : X ⟶ Y} {f₂ : Y ⟶ Z} {g₁ : X ⟶ Y'} {g₂ : Y' ⟶ Z} (hk : g₁ ≫ g₂ = f₁ ≫ f₂)
    (N : Modules.{u, u} B S hS Z.1 Z.2) (M : Modules.{u, u} B S hS X.1 X.2)
    (w : (modulePullback B S hS (g₁ ≫ g₂)).obj N ⟶ M) :
    (modulePullbackAdjunction B S hS (g₁ ≫ g₂)).homEquiv N M w ≫
        (eqToHom (congrArg (fun m => modulePushforward B S hS m) hk)).app M =
      (modulePullbackAdjunction B S hS (f₁ ≫ f₂)).homEquiv N M
        ((eqToHom (congrArg (modulePullback B S hS) hk.symm)).app N ≫ w) := by
  revert w hk
  generalize f₁ ≫ f₂ = k
  generalize g₁ ≫ g₂ = k'
  intro hk w
  subst hk
  simp

/-- The transpose of `u : f^*M ⟶ A` followed by `f_*` of the unit of `g` and the comparison of
direct images is the transpose along `g ≫ f` of `g^*u`, read through the comparison of inverse
images. -/
theorem homEquiv_comp_unit_comp_compIso {X Y Z : AlgebraicSpaces B S hS} (g : X ⟶ Y) (f : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (A : Modules.{u, u} B S hS Y.1 Y.2)
    (u : (modulePullback B S hS f).obj M ⟶ A) :
    (modulePullbackAdjunction B S hS f).homEquiv M A u ≫
        (modulePushforward B S hS f).map ((modulePullbackAdjunction B S hS g).unit.app A) ≫
        (modulePushforwardCompIso B S hS g f).hom.app ((modulePullback B S hS g).obj A) =
      (modulePullbackAdjunction B S hS (g ≫ f)).homEquiv M ((modulePullback B S hS g).obj A)
        ((modulePullbackCompIso B S hS g f).inv.app M ≫ (modulePullback B S hS g).map u) := by
  rw [homEquiv_modulePullbackCompIso_inv_app_comp, ← Category.assoc,
    ← Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_unit _ _ _ ((modulePullback B S hS g).map u),
    Adjunction.unit_naturality]
  rfl

/-- **The coherence of the comparisons of inverse images around a commutative square.**  For
morphisms `a : V ⟶ P`, `b : U' ⟶ P`, `c : U ⟶ V`, `d : U ⟶ U'` with `c ≫ a = d ≫ b` over a common
`sP : P ⟶ X₀`, and morphisms `πA` and `πB` out of the inverse images of a module `F` on `X₀`
identified over `U` by `θ`, the two ways of reading `(c ≫ a)^*(sP^*F)` into `c^*A` agree. -/
theorem modulePullback_square_coherence {X₀ P V U' U : AlgebraicSpaces B S hS} (sP : P ⟶ X₀)
    {sV : V ⟶ X₀} {sU' : U' ⟶ X₀} {sU : U ⟶ X₀} (a : V ⟶ P) (b : U' ⟶ P) (c : U ⟶ V)
    (d : U ⟶ U') (comm : c ≫ a = d ≫ b) (ha : a ≫ sP = sV) (hb : b ≫ sP = sU')
    (hc : c ≫ sV = sU) (hd : d ≫ sU' = sU) (F : Modules.{u, u} B S hS X₀.1 X₀.2)
    {A : Modules.{u, u} B S hS V.1 V.2} {B' : Modules.{u, u} B S hS U'.1 U'.2}
    (πA : (modulePullback B S hS sV).obj F ⟶ A) (πB : (modulePullback B S hS sU').obj F ⟶ B')
    (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)
    (hθ : (modulePullbackTriangle B S hS hd).hom.app F ≫ (modulePullback B S hS d).map πB ≫ θ =
      (modulePullbackTriangle B S hS hc).hom.app F ≫ (modulePullback B S hS c).map πA) :
    (modulePullbackCompIso B S hS c a).inv.app ((modulePullback B S hS sP).obj F) ≫
        (modulePullback B S hS c).map ((modulePullbackTriangle B S hS ha).inv.app F ≫ πA) =
      (eqToHom (congrArg (modulePullback B S hS) comm)).app ((modulePullback B S hS sP).obj F) ≫
        ((modulePullbackCompIso B S hS d b).inv.app ((modulePullback B S hS sP).obj F) ≫
          (modulePullback B S hS d).map ((modulePullbackTriangle B S hS hb).inv.app F ≫ πB)) ≫
        θ := by
  have hkr : (c ≫ a) ≫ sP = sU := by rw [Category.assoc, ha, hc]
  have hkr' : (d ≫ b) ≫ sP = sU := by rw [Category.assoc, hb, hd]
  have T : ∀ {W W' : AlgebraicSpaces B S hS} (x : W ⟶ W') (y : W' ⟶ P),
      (modulePullbackCompIso B S hS x y).inv.app ((modulePullback B S hS sP).obj F) =
        (modulePullbackTriangle B S hS (rfl : x ≫ y = x ≫ y)).hom.app
          ((modulePullback B S hS sP).obj F) := fun x y => by
    rw [modulePullbackTriangle_rfl, Iso.symm_hom]
  rw [T c a, T d b]
  exact CategoryTheory.square_coherence (modulePullbackTriangle B S hS ha)
    (modulePullbackTriangle B S hS hb) (modulePullbackTriangle B S hS hc)
    (modulePullbackTriangle B S hS hd) (modulePullbackTriangle B S hS (rfl : c ≫ a = c ≫ a))
    (modulePullbackTriangle B S hS (rfl : d ≫ b = d ≫ b)) (modulePullbackTriangle B S hS hkr)
    (modulePullbackTriangle B S hS hkr') (congrArg (modulePullback B S hS) comm)
    (congrArg (modulePullback B S hS) comm.symm) F πA πB θ
    (modulePullbackTriangle_inv_app_assoc B S hS rfl ha hc hkr F)
    (modulePullbackTriangle_inv_app_assoc B S hS rfl hb hd hkr' F)
    (modulePullbackTriangle_congr_left comm hkr hkr') hθ

namespace ThickeningPushoutSpaces

variable {Z Z' Y Y' : BigFppfOver B S hS} {i : Z ⟶ Z'} {f : Z ⟶ Y} {g : Z' ⟶ Y'} {h : Y ⟶ Y'}
  {P V U' U : AlgebraicSpaces B S hS} {p : P ⟶ (schemeSpaceFunctor B S hS).obj Y'}
  {pV : V ⟶ (schemeSpaceFunctor B S hS).obj Y} {pU' : U' ⟶ (schemeSpaceFunctor B S hS).obj Z'}
  {pU : U ⟶ (schemeSpaceFunctor B S hS).obj Z} {a : V ⟶ P} {b : U' ⟶ P} {c : U ⟶ V} {d : U ⟶ U'}

variable (E : ThickeningPushoutSpaces i f g h p pV pU' pU a b c d)
include E

section Quotient

variable {X₀ : AlgebraicSpaces B S hS} (sP : P ⟶ X₀) {sV : V ⟶ X₀} {sU' : U' ⟶ X₀}
  {sU : U ⟶ X₀} (ha : a ≫ sP = sV) (hb : b ≫ sP = sU') (hc : c ≫ sV = sU) (hd : d ≫ sU' = sU)
  (F : Modules.{u, u} B S hS X₀.1 X₀.2) {A : Modules.{u, u} B S hS V.1 V.2}
  {B' : Modules.{u, u} B S hS U'.1 U'.2} (πA : (modulePullback B S hS sV).obj F ⟶ A)
  (πB : (modulePullback B S hS sU').obj F ⟶ B')
  (θ : (modulePullback B S hS d).obj B' ⟶ (modulePullback B S hS c).obj A)

/-- **The two maps from `sP^*F` to the two halves of the glued module agree in
`(c ≫ a)_*c^*A`.** -/
theorem glueLift_compat
    (hθ : (modulePullbackTriangle B S hS hd).hom.app F ≫ (modulePullback B S hS d).map πB ≫ θ =
      (modulePullbackTriangle B S hS hc).hom.app F ≫ (modulePullback B S hS c).map πA) :
    (modulePullbackAdjunction B S hS a).homEquiv ((modulePullback B S hS sP).obj F) A
        ((modulePullbackTriangle B S hS ha).inv.app F ≫ πA) ≫
      ((modulePushforward B S hS a).map (unitC c A) ≫
        (modulePushforwardCompIso B S hS c a).hom.app ((modulePullback B S hS c).obj A)) =
    (modulePullbackAdjunction B S hS b).homEquiv ((modulePullback B S hS sP).obj F) B'
        ((modulePullbackTriangle B S hS hb).inv.app F ≫ πB) ≫
      (((modulePushforward B S hS b).map (unitD d B') ≫
          (modulePushforwardCompIso B S hS d b).hom.app ((modulePullback B S hS d).obj B')) ≫
        (eqToHom (congrArg (fun m => modulePushforward B S hS m) E.comm.symm)).app
          ((modulePullback B S hS d).obj B') ≫
        (modulePushforward B S hS (c ≫ a)).map θ) := by
  have key := modulePullback_square_coherence sP a b c d E.comm.symm.symm ha hb hc hd F πA πB θ hθ
  exact CategoryTheory.square_homEquiv_compat (modulePullbackAdjunction B S hS a)
    (modulePullbackAdjunction B S hS b) (modulePullbackAdjunction B S hS c)
    (modulePullbackAdjunction B S hS d) (modulePullbackAdjunction B S hS (c ≫ a))
    (modulePullbackAdjunction B S hS (d ≫ b)) (modulePushforwardCompIso B S hS c a)
    (modulePushforwardCompIso B S hS d b) (modulePullbackCompIso B S hS c a)
    (modulePullbackCompIso B S hS d b) _ _
    (fun M A' u => homEquiv_comp_unit_comp_compIso c a M A' u)
    (fun M A' u => homEquiv_comp_unit_comp_compIso d b M A' u)
    (fun N M w => homEquiv_comp_eqToHom_modulePushforward E.comm.symm N M w)
    ((modulePullback B S hS sP).obj F) _ _ θ (unitC c A) (unitD d B') rfl rfl _ rfl key

end Quotient

end ThickeningPushoutSpaces

end AlgebraicGeometry.Space

end
