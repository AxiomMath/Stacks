module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Left derived functors of a coherent pullback pseudofunctor datum

Let `P` be a pullback pseudofunctor datum (`CategoryTheory.PullbackData`) on a family of
categories `H a`, and let `Q a : H a ⥤ D a` be localizations.  If each inverse image along `f`
has a left derived functor `L f` with comparison `c f : Q b ⋙ L f ⟶ P.pull f ⋙ Q a`, the universal
property of left derived functors gives comparisons `L g ⋙ L f ⟶ L (f ≫ g)` and `𝟭 ⟶ L (𝟙 a)`.
This file shows that, when they are invertible, they make the `L f` a pullback pseudofunctor
datum which is coherent as soon as `P` is.  It also carries a coherent datum of additive functors
over to the homotopy categories of cochain complexes, and transports a datum along isomorphisms of
its inverse images.

## Main definitions

* `CategoryTheory.PullbackData.derivedComp` and `CategoryTheory.PullbackData.derivedIdLift`: the
  induced comparisons.
* `CategoryTheory.PullbackData.leftDerived`: the left derived datum.
* `CategoryTheory.PullbackData.transport`: a datum transported along isomorphisms of its inverse
  images.
* `CategoryTheory.PullbackData.toHomotopy`: a datum of additive functors on the homotopy
  categories of cochain complexes.

## Main results

* `CategoryTheory.PullbackData.leftDerived_isCoherent`: **the left derived datum of a coherent
  datum is coherent.**
* `CategoryTheory.PullbackData.transport_isCoherent` and
  `CategoryTheory.PullbackData.toHomotopy_isCoherent`: coherence passes along transport and to
  the homotopy categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂ v₃ u₃

variable {A : Type u₁} [Category.{v₁} A] {H : A → Type u₂} [∀ a, Category.{v₂} (H a)]
  {D : A → Type u₃} [∀ a, Category.{v₃} (D a)]
  (Q : ∀ a, H a ⥤ D a) (W : ∀ a, MorphismProperty (H a)) [∀ a, (Q a).IsLocalization (W a)]
  (P : PullbackData A H) (L : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
  (c : ∀ {a b : A} (f : a ⟶ b), Q b ⋙ L f ⟶ P.pull f ⋙ Q a)
  [hL : ∀ {a b : A} (f : a ⟶ b), (L f).IsLeftDerivedFunctor (c f) (W b)]

/-- The comparison of the composite of two left derived functors with the underived inverse
image along the composite: the comparison for `g`, pushed forward by `L f`; the comparison for
`f`; and the underived composition comparison. -/
def derivedCompCounit {a b d : A} (f : a ⟶ b) (g : b ⟶ d) :
    Q d ⋙ (L g ⋙ L f) ⟶ P.pull (f ≫ g) ⋙ Q a where
  app X := (L f).map ((c g).app X) ≫ (c f).app ((P.pull g).obj X) ≫
    (Q a).map ((P.compIso f g).inv.app X)
  naturality X Y φ := by
    have h₁ := (c g).naturality φ
    have h₂ := (c f).naturality ((P.pull g).map φ)
    have h₃ := (P.compIso f g).inv.naturality φ
    dsimp at h₁ h₂ h₃
    have e₁ : (L f).map ((L g).map ((Q d).map φ)) ≫ (L f).map ((c g).app Y) =
        (L f).map ((c g).app X) ≫ (L f).map ((Q b).map ((P.pull g).map φ)) := by
      rw [← Functor.map_comp, ← Functor.map_comp, h₁]
    have e₃ : (Q a).map ((P.pull f).map ((P.pull g).map φ)) ≫
        (Q a).map ((P.compIso f g).inv.app Y) =
        (Q a).map ((P.compIso f g).inv.app X) ≫ (Q a).map ((P.pull (f ≫ g)).map φ) := by
      rw [← Functor.map_comp, ← Functor.map_comp, h₃]
    simp only [Functor.comp_map, Category.assoc]
    rw [reassoc_of% e₁, reassoc_of% h₂, e₃]

/-- The canonical comparison `L g ⋙ L f ⟶ L (f ≫ g)`, from the universal property of the left
derived functor `L (f ≫ g)`. -/
def derivedComp {a b d : A} (f : a ⟶ b) (g : b ⟶ d) : L g ⋙ L f ⟶ L (f ≫ g) :=
  (L (f ≫ g)).leftDerivedLift (c (f ≫ g)) (W d) (L g ⋙ L f) (derivedCompCounit Q P L c f g)

/-- The comparison `derivedComp` followed by the comparison for `f ≫ g`, on the image of an
object under the localization, is the composite of the comparisons for `g` and `f` with the
underived composition comparison. -/
@[reassoc]
theorem derivedComp_fac {a b d : A} (f : a ⟶ b) (g : b ⟶ d) (X : H d) :
    (derivedComp Q W P L c f g).app ((Q d).obj X) ≫ (c (f ≫ g)).app X =
      (L f).map ((c g).app X) ≫ (c f).app ((P.pull g).obj X) ≫
        (Q a).map ((P.compIso f g).inv.app X) :=
  (L (f ≫ g)).leftDerived_fac_app (c (f ≫ g)) (W d) (L g ⋙ L f) _ X

/-- The comparison of the underived inverse image along an identity with the localization. -/
def derivedIdCounit (a : A) : Q a ⋙ 𝟭 (D a) ⟶ P.pull (𝟙 a) ⋙ Q a where
  app X := (Q a).map ((P.idIso a).inv.app X)
  naturality X Y φ := by
    have h := (P.idIso a).inv.naturality φ
    dsimp at h
    simp only [Functor.comp_map, Functor.id_map]
    rw [← (Q a).map_comp, ← (Q a).map_comp, h]

/-- The canonical comparison `𝟭 ⟶ L (𝟙 a)`. -/
def derivedIdLift (a : A) : 𝟭 (D a) ⟶ L (𝟙 a) :=
  (L (𝟙 a)).leftDerivedLift (c (𝟙 a)) (W a) (𝟭 (D a)) (derivedIdCounit Q P a)

/-- The comparison `derivedIdLift` followed by the comparison for `𝟙 a`, on the image of an
object under the localization, is the image of the underived unit law. -/
@[reassoc]
theorem derivedIdLift_fac (a : A) (X : H a) :
    (derivedIdLift Q W P L c a).app ((Q a).obj X) ≫ (c (𝟙 a)).app X =
      (Q a).map ((P.idIso a).inv.app X) :=
  (L (𝟙 a)).leftDerived_fac_app (c (𝟙 a)) (W a) (𝟭 (D a)) _ X

variable [hcomp : ∀ {a b d : A} (f : a ⟶ b) (g : b ⟶ d), IsIso (derivedComp Q W P L c f g)]
  [hid : ∀ a : A, IsIso (derivedIdLift Q W P L c a)]

/-- **The left derived pullback pseudofunctor datum**: the left derived functors, with the unit
law and the composition comparison induced by the universal property of left derived functors
from those of the underived datum. -/
abbrev leftDerived : PullbackData A D where
  pull f := L f
  idIso a := (asIso (derivedIdLift Q W P L c a)).symm
  compIso f g := (asIso (derivedComp Q W P L c f g)).symm

/-- The inverse image of the left derived datum along `f` is the left derived functor `L f`. -/
theorem leftDerived_pull {a b : A} (f : a ⟶ b) : (leftDerived Q W P L c).pull f = L f := rfl

/-- The inverse of the composition comparison of the left derived datum along a presented
composite `f ≫ g = k`, followed by the comparison for `k`, is the composite of the comparisons for
`g` and `f` with the inverse of the underived composition comparison. -/
@[reassoc]
theorem leftDerived_triangle_inv_fac {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) (X : H d) :
    ((leftDerived Q W P L c).triangle hk).inv.app ((Q d).obj X) ≫ (c k).app X =
      (L f).map ((c g).app X) ≫ (c f).app ((P.pull g).obj X) ≫
        (Q a).map ((P.triangle hk).inv.app X) := by
  subst hk
  rw [triangle_rfl, triangle_rfl]
  exact derivedComp_fac Q W P L c f g X

/-- The unit law of the left derived datum, on the image of an object under the localization, is
the comparison for `𝟙 a` followed by the image of the underived unit law. -/
theorem leftDerived_idIso_hom_app (a : A) (X : H a) :
    ((leftDerived Q W P L c).idIso a).hom.app ((Q a).obj X) =
      (c (𝟙 a)).app X ≫ (Q a).map ((P.idIso a).hom.app X) := by
  show (asIso (derivedIdLift Q W P L c a)).inv.app ((Q a).obj X) = _
  rw [← cancel_epi ((asIso (derivedIdLift Q W P L c a)).hom.app ((Q a).obj X)),
    Iso.hom_inv_id_app]
  show 𝟙 _ = (derivedIdLift Q W P L c a).app ((Q a).obj X) ≫ _
  rw [reassoc_of% (derivedIdLift_fac Q W P L c a X), ← (Q a).map_comp, Iso.inv_hom_id_app]
  exact ((Q a).map_id X).symm

/-- For a coherent datum, the inverse of the comparison along `𝟙 a ≫ g = g` is the unit law. -/
private theorem triangle_inv_app_of_id {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
    {P' : PullbackData A M} (hP : P'.IsCoherent) {a b : A} (g : a ⟶ b) (hk : 𝟙 a ≫ g = g)
    (X : M b) : (P'.triangle hk).inv.app X = (P'.idIso a).hom.app ((P'.pull g).obj X) := by
  have h := congrArg (fun e : P'.pull g ≅ P'.pull g ⋙ P'.pull (𝟙 a) => e.inv.app X)
    (hP.triangle_id g hk)
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at h
  exact h.trans (Category.comp_id _)

/-- For a coherent datum, the two ways of breaking a triple composite into three steps have the
same inverse comparison on an object. -/
private theorem triangle_inv_app_comp {M : A → Type u₂} [∀ a, Category.{v₂} (M a)]
    {P' : PullbackData A M} (hP : P'.IsCoherent) {a b c d : A} {f : a ⟶ b} {g : b ⟶ c}
    {p : c ⟶ d} {k : a ⟶ c} {q : b ⟶ d} {r : a ⟶ d} (hk : f ≫ g = k) (hq : g ≫ p = q)
    (hr : f ≫ q = r) (hkr : k ≫ p = r) (X : M d) :
    (P'.triangle hk).inv.app ((P'.pull p).obj X) ≫ (P'.triangle hkr).inv.app X =
      (P'.pull f).map ((P'.triangle hq).inv.app X) ≫ (P'.triangle hr).inv.app X := by
  have h := congrArg
    (fun e : P'.pull r ≅ P'.pull p ⋙ P'.pull g ⋙ P'.pull f => e.inv.app X)
    (hP.triangle_comp hk hq hr hkr)
  simpa using h

/-- **The left derived datum of a coherent pullback pseudofunctor datum is coherent.** -/
theorem leftDerived_isCoherent (hP : P.IsCoherent) : (leftDerived Q W P L c).IsCoherent where
  triangle_id {a b} g hk := by
    refine Iso.ext ?_
    rw [← Iso.inv_eq_inv]
    refine Functor.leftDerived_ext (L g) (c g) (W b) _ _ _ (NatTrans.ext (funext fun X => ?_))
    have h₁ := leftDerived_triangle_inv_fac Q W P L c hk X
    have h₂ : (L (𝟙 a)).map ((c g).app X) ≫
        ((leftDerived Q W P L c).idIso a).hom.app ((Q a).obj ((P.pull g).obj X)) =
        ((leftDerived Q W P L c).idIso a).hom.app ((L g).obj ((Q b).obj X)) ≫ (c g).app X :=
      ((leftDerived Q W P L c).idIso a).hom.naturality ((c g).app X)
    have h₃ := leftDerived_idIso_hom_app Q W P L c a ((P.pull g).obj X)
    show ((leftDerived Q W P L c).triangle hk).inv.app ((Q b).obj X) ≫ (c g).app X =
      (((leftDerived Q W P L c).idIso a).hom.app ((L g).obj ((Q b).obj X)) ≫ 𝟙 _) ≫ (c g).app X
    rw [Category.comp_id, ← h₂, h₃, h₁, triangle_inv_app_of_id hP g hk]
  triangle_comp {a b d e} f g p k q r hk hq hr hkr := by
    refine Iso.ext ?_
    rw [← Iso.inv_eq_inv]
    refine Functor.leftDerived_ext (L r) (c r) (W e) _ _ _ (NatTrans.ext (funext fun X => ?_))
    have hk' := leftDerived_triangle_inv_fac Q W P L c hk ((P.pull p).obj X)
    have hkr' := leftDerived_triangle_inv_fac Q W P L c hkr X
    have hq' := leftDerived_triangle_inv_fac Q W P L c hq X
    have hr' := leftDerived_triangle_inv_fac Q W P L c hr X
    have n₁ := ((leftDerived Q W P L c).triangle hk).inv.naturality ((c p).app X)
    have n₂ := (c f).naturality ((P.triangle hq).inv.app X)
    have h := triangle_inv_app_comp hP hk hq hr hkr X
    dsimp at hk' hkr' hq' hr' n₁ n₂
    have n₁' : (L f).map ((L g).map ((c p).app X)) ≫
        ((leftDerived Q W P L c).triangle hk).inv.app ((Q d).obj ((P.pull p).obj X)) =
        ((leftDerived Q W P L c).triangle hk).inv.app ((L p).obj ((Q e).obj X)) ≫
          (L k).map ((c p).app X) := n₁
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.assoc, Category.id_comp]
    have hq'' : (L f).map (((leftDerived Q W P L c).triangle hq).inv.app ((Q e).obj X)) ≫
        (L f).map ((c q).app X) =
        (L f).map ((L g).map ((c p).app X)) ≫ (L f).map ((c g).app ((P.pull p).obj X)) ≫
          (L f).map ((Q b).map ((P.triangle hq).inv.app X)) := by
      simpa only [Functor.map_comp] using congrArg (L f).map hq'
    rw [hkr', hr', ← reassoc_of% n₁', reassoc_of% hk', reassoc_of% hq'', reassoc_of% n₂,
      ← (Q a).map_comp, ← (Q a).map_comp, h]

/-! ### Transport along isomorphisms of the inverse images -/

section Transport

variable {M : A → Type u₂} [∀ a, Category.{v₂} (M a)] (P' : PullbackData A M)
  (pull' : ∀ {a b : A}, (a ⟶ b) → (M b ⥤ M a)) (ε : ∀ {a b : A} (f : a ⟶ b), pull' f ≅ P'.pull f)

/-- **A pullback pseudofunctor datum transported along isomorphisms of its inverse images.** -/
abbrev transport : PullbackData A M where
  pull f := pull' f
  idIso a := ε (𝟙 a) ≪≫ P'.idIso a
  compIso f g := ε (f ≫ g) ≪≫ P'.compIso f g ≪≫
    (Functor.isoWhiskerLeft (pull' g) (ε f) ≪≫ Functor.isoWhiskerRight (ε g) (P'.pull f)).symm

/-- The composition comparison of the transported datum along a presented composite is the
comparison of the original datum conjugated by the given isomorphisms of inverse images. -/
theorem transport_triangle {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d} (hk : f ≫ g = k) :
    (transport P' pull' ε).triangle hk = ε k ≪≫ P'.triangle hk ≪≫
      (Functor.isoWhiskerLeft (pull' g) (ε f) ≪≫
        Functor.isoWhiskerRight (ε g) (P'.pull f)).symm := by
  subst hk
  rw [triangle_rfl, triangle_rfl]

/-- The transport of a coherent pullback pseudofunctor datum is coherent. -/
theorem transport_isCoherent (hP : P'.IsCoherent) : (transport P' pull' ε).IsCoherent where
  triangle_id {a b} g hk := by
    rw [transport_triangle, hP.triangle_id g hk]
    ext X
    have n₁ := (P'.idIso a).inv.naturality ((ε g).hom.app X)
    dsimp at n₁ ⊢
    simp only [Category.id_comp]
    rw [reassoc_of% n₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, Functor.map_id,
      Category.id_comp]
  triangle_comp {a b d e} f g p k q r hk hq hr hkr := by
    rw [transport_triangle, transport_triangle, transport_triangle, transport_triangle]
    have h := congrArg Iso.hom (hP.triangle_comp hk hq hr hkr)
    ext X
    have hX := NatTrans.congr_app h X
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id] at hX
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.associator_hom_app,
      Category.comp_id, Category.assoc, Iso.trans_inv]
    have n₁ := (P'.triangle hk).hom.naturality ((ε p).inv.app X)
    have n₂ := (ε f).inv.naturality ((ε q).hom.app X ≫ (P'.triangle hq).hom.app X ≫
      (P'.pull g).map ((ε p).inv.app X) ≫ (ε g).inv.app ((pull' p).obj X))
    dsimp at n₁ n₂
    rw [Iso.inv_hom_id_app_assoc, reassoc_of% n₁, reassoc_of% hX, ← n₂]
    simp only [Functor.map_comp, Category.assoc]
    rw [← (P'.pull f).map_comp_assoc ((ε q).inv.app X) ((ε q).hom.app X), Iso.inv_hom_id_app,
      Functor.map_id, Category.id_comp]

end Transport

/-! ### Passage to the homotopy categories -/

section Homotopy

variable {M : A → Type u₂} [∀ a, Category.{v₂} (M a)] [∀ a, Preadditive (M a)]
  (P' : PullbackData A M) [hadd : ∀ {a b : A} (f : a ⟶ b), (P'.pull f).Additive]

/-- An isomorphism of additive functors, on the homotopy categories of cochain complexes. -/
def homotopyIso {V W : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
    {F G : V ⥤ W} [F.Additive] [G.Additive] (e : F ≅ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ≅ G.mapHomotopyCategory (ComplexShape.up ℤ) where
  hom := NatTrans.mapHomotopyCategory e.hom _
  inv := NatTrans.mapHomotopyCategory e.inv _
  hom_inv_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id, NatTrans.mapHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id, NatTrans.mapHomotopyCategory_id]

/-- On a cochain complex, `homotopyIso e` is the image in the homotopy category of `e` applied
degreewise. -/
@[simp]
theorem homotopyIso_hom_app_quotient {V W : Type*} [Category V] [Preadditive V] [Category W]
    [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : CochainComplex V ℤ) :
    (homotopyIso e).hom.app ((HomotopyCategory.quotient V _).obj K) =
      (HomotopyCategory.quotient W _).map ((NatTrans.mapHomologicalComplex e.hom _).app K) :=
  rfl

/-- On a cochain complex, the inverse of `homotopyIso e` is the image in the homotopy category of
the inverse of `e` applied degreewise. -/
@[simp]
theorem homotopyIso_inv_app_quotient {V W : Type*} [Category V] [Preadditive V] [Category W]
    [Preadditive W] {F G : V ⥤ W} [F.Additive] [G.Additive] (e : F ≅ G)
    (K : CochainComplex V ℤ) :
    (homotopyIso e).inv.app ((HomotopyCategory.quotient V _).obj K) =
      (HomotopyCategory.quotient W _).map ((NatTrans.mapHomologicalComplex e.inv _).app K) :=
  rfl

/-- The functor induced on the homotopy categories by a composite of additive functors is the
composite of the induced functors. -/
def homotopyCompIso {V W W' : Type*} [Category V] [Preadditive V] [Category W] [Preadditive W]
    [Category W'] [Preadditive W'] (F : V ⥤ W) (G : W ⥤ W') [F.Additive] [G.Additive] :
    (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ G.mapHomotopyCategory (ComplexShape.up ℤ) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) _).symm

/-- On a cochain complex, `homotopyCompIso F G` is the identity. -/
@[simp]
theorem homotopyCompIso_hom_app_quotient {V W W' : Type*} [Category V] [Preadditive V]
    [Category W] [Preadditive W] [Category W'] [Preadditive W'] (F : V ⥤ W) (G : W ⥤ W')
    [F.Additive] [G.Additive] (K : CochainComplex V ℤ) :
    (homotopyCompIso F G).hom.app ((HomotopyCategory.quotient V _).obj K) = 𝟙 _ := by
  simp [homotopyCompIso, Functor.mapHomotopyCategoryCompIso,
    Functor.mapHomologicalComplexCompIso]
  rfl

/-- On a cochain complex, the inverse of `homotopyCompIso F G` is the identity. -/
@[simp]
theorem homotopyCompIso_inv_app_quotient {V W W' : Type*} [Category V] [Preadditive V]
    [Category W] [Preadditive W] [Category W'] [Preadditive W'] (F : V ⥤ W) (G : W ⥤ W')
    [F.Additive] [G.Additive] (K : CochainComplex V ℤ) :
    (homotopyCompIso F G).inv.app ((HomotopyCategory.quotient V _).obj K) = 𝟙 _ := by
  simp [homotopyCompIso, Functor.mapHomotopyCategoryCompIso,
    Functor.mapHomologicalComplexCompIso]
  rfl

/-- The functor induced on the homotopy categories by the identity functor is the identity. -/
def homotopyIdIso (V : Type*) [Category V] [Preadditive V] :
    (𝟭 V).mapHomotopyCategory (ComplexShape.up ℤ) ≅ 𝟭 (HomotopyCategory V (ComplexShape.up ℤ)) :=
  Quotient.natIsoLift _ (NatIso.ofComponents (fun K => Iso.refl _) (fun {K L} φ => by
    refine (Category.comp_id _).trans ?_
    refine Eq.trans ?_ (Category.id_comp _).symm
    rfl))

/-- On a cochain complex, `homotopyIdIso V` is the identity. -/
@[simp]
theorem homotopyIdIso_hom_app_quotient (V : Type*) [Category V] [Preadditive V]
    (K : CochainComplex V ℤ) :
    (homotopyIdIso V).hom.app ((HomotopyCategory.quotient V _).obj K) = 𝟙 _ :=
  rfl

/-- On a cochain complex, the inverse of `homotopyIdIso V` is the identity. -/
@[simp]
theorem homotopyIdIso_inv_app_quotient (V : Type*) [Category V] [Preadditive V]
    (K : CochainComplex V ℤ) :
    (homotopyIdIso V).inv.app ((HomotopyCategory.quotient V _).obj K) = 𝟙 _ :=
  rfl

/-- **A pullback pseudofunctor datum of additive functors, on the homotopy categories of cochain
complexes.** -/
def toHomotopy : PullbackData A (fun a => HomotopyCategory (M a) (ComplexShape.up ℤ)) where
  pull f := (P'.pull f).mapHomotopyCategory _
  idIso a := homotopyIso (P'.idIso a) ≪≫ homotopyIdIso (M a)
  compIso f g := homotopyIso (P'.compIso f g) ≪≫ homotopyCompIso (P'.pull g) (P'.pull f)

/-- The inverse image of `toHomotopy P'` along `f` is the functor induced on the homotopy
categories by the inverse image of `P'` along `f`. -/
theorem toHomotopy_pull {a b : A} (f : a ⟶ b) :
    (toHomotopy P').pull f = (P'.pull f).mapHomotopyCategory _ := rfl

/-- On a cochain complex, the inverse of the composition comparison of `toHomotopy P'` along a
presented composite is the image in the homotopy category of that of `P'` applied degreewise. -/
theorem toHomotopy_triangle_inv_app {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) (K : CochainComplex (M d) ℤ) :
    ((toHomotopy P').triangle hk).inv.app ((HomotopyCategory.quotient (M d) _).obj K) =
      (HomotopyCategory.quotient (M a) _).map
        ((NatTrans.mapHomologicalComplex (P'.triangle hk).inv _).app K) := by
  subst hk
  rw [triangle_rfl, triangle_rfl]
  exact (Category.id_comp _).trans rfl

/-- On a cochain complex, the unit law of `toHomotopy P'` is the image in the homotopy category of
the unit law of `P'` applied degreewise. -/
theorem toHomotopy_idIso_hom_app (a : A) (K : CochainComplex (M a) ℤ) :
    ((toHomotopy P').idIso a).hom.app ((HomotopyCategory.quotient (M a) _).obj K) =
      (HomotopyCategory.quotient (M a) _).map
        ((NatTrans.mapHomologicalComplex (P'.idIso a).hom _).app K) :=
  (Category.comp_id _).trans rfl

/-- If `P'` is coherent, then so is the datum `toHomotopy P'` on the homotopy categories. -/
theorem toHomotopy_isCoherent (hP : P'.IsCoherent) : (toHomotopy P').IsCoherent where
  triangle_id {a b} g hk := by
    refine Iso.ext ?_
    rw [← Iso.inv_eq_inv]
    refine NatTrans.ext (funext fun X => ?_)
    obtain ⟨K⟩ := X
    show ((toHomotopy P').triangle hk).inv.app ((HomotopyCategory.quotient (M b) _).obj K) =
      ((toHomotopy P').idIso a).hom.app (((toHomotopy P').pull g).obj
        ((HomotopyCategory.quotient (M b) _).obj K)) ≫ 𝟙 _
    rw [Category.comp_id, toHomotopy_triangle_inv_app]
    show _ = ((toHomotopy P').idIso a).hom.app ((HomotopyCategory.quotient (M a) _).obj
      (((P'.pull g).mapHomologicalComplex _).obj K))
    rw [toHomotopy_idIso_hom_app]
    congr 1
    ext i
    exact triangle_inv_app_of_id hP g hk _
  triangle_comp {a b d e} f g p k q r hk hq hr hkr := by
    refine Iso.ext ?_
    rw [← Iso.inv_eq_inv]
    refine NatTrans.ext (funext fun X => ?_)
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp]
    have e₁ := toHomotopy_triangle_inv_app P' hk (((P'.pull p).mapHomologicalComplex _).obj K)
    have e₂ := toHomotopy_triangle_inv_app P' hkr K
    have e₃ := toHomotopy_triangle_inv_app P' hq K
    have e₄ := toHomotopy_triangle_inv_app P' hr K
    refine (congrArg₂ (· ≫ ·) e₁ e₂).trans (Eq.trans ?_ (congrArg₂ (· ≫ ·)
      (congrArg ((P'.pull f).mapHomotopyCategory _).map e₃).symm e₄.symm))
    have key : (NatTrans.mapHomologicalComplex (P'.triangle hk).inv _).app
          (((P'.pull p).mapHomologicalComplex _).obj K) ≫
        (NatTrans.mapHomologicalComplex (P'.triangle hkr).inv _).app K =
        ((P'.pull f).mapHomologicalComplex _).map
          ((NatTrans.mapHomologicalComplex (P'.triangle hq).inv _).app K) ≫
        (NatTrans.mapHomologicalComplex (P'.triangle hr).inv _).app K := by
      ext i
      simpa using triangle_inv_app_comp hP hk hq hr hkr (K.X i)
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ _).map key).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _))

end Homotopy

end CategoryTheory.PullbackData
