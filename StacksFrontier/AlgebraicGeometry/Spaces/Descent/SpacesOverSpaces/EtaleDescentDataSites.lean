module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.Effective
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleRepresentableTransformation

/-!
# Étale descent data of algebraic spaces as descent data of spaces-étale sites

Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S`, and let `(U/X, φ)` be a descent datum
relative to `f` (Stacks 0ADG) whose underlying space `U` is étale over `X`. The gluing
isomorphism `φ` moves a point of `U` lying over a point `x₁` of `X` to a point of `U` lying over
any point `x₂` of `X` with the same image in `Y`. Applied to the two projections of a fibre
product, this gives, for every algebraic space `Y'` with two maps `f₁, f₂ : Y' ⟶ X` agreeing
over `Y`, a morphism `f₁^* U ⟶ f₂^* U` over `Y'`; these morphisms are compatible with base
change along `Y'' ⟶ Y'`, trivial when `f₁ = f₂`, and compose, by the cocycle condition. They are
therefore a descent datum for the pseudofunctor of spaces-étale sites
`AlgebraicGeometry.Space.spacesEtaleSitePseudofunctor` relative to `f`, in the sense of
`CategoryTheory.Pseudofunctor.DescentData`. This is the first half of the translation in the
proof of Stacks 0GG0, the passage from a descent datum of spaces to a descent datum for étale
sheaves, the second half being the Yoneda embedding
`AlgebraicGeometry.Space.spacesEtaleYonedaStrongTrans`.

## Main definitions

* `AlgebraicGeometry.Space.Descent.HomDescentData.pointMove`: the move operation of a descent
  datum for one morphism, on maps of presheaves.
* `AlgebraicGeometry.Space.Descent.HomDescentData.etaleObj`: the underlying space of a descent
  datum with étale underlying space, as an object of the spaces-étale site of the source.
* `AlgebraicGeometry.Space.Descent.HomDescentData.toSpacesEtaleDescentData`: the descent datum
  for the pseudofunctor of spaces-étale sites.

## Implementation notes

The fibres of `AlgebraicGeometry.Space.spacesEtaleSitePseudofunctor` are the spaces-étale sites
only up to unfolding, so the three axioms of the descent datum are proved for the underlying
morphisms of fibre products, `AlgebraicGeometry.Space.Descent.HomDescentData.etaleLift_self`,
`…_comp` and `…_pull`, and transferred along the two extensionality lemmas of full subcategories
and slices.

## References

* [Stacks Project, Tag 0ADG](https://stacks.math.columbia.edu/tag/0ADG)
* [Stacks Project, Tag 0GG0](https://stacks.math.columbia.edu/tag/0GG0)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for discrete limits of presheaves on the big fppf site is deep
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_etaleDescentDataSites
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

namespace HomDescentData

section Move

variable {P T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : P ⟶ T} {hT : IsAlgebraicSpace B S hS T}
  {hP : IsAlgebraicSpace B S hS P} (D : HomDescentData.{u, 0} p hT hP)
  {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The move operation of a descent datum for one morphism `p : P ⟶ T`, on maps of presheaves:
a map `a` to the underlying space `U` of the datum, together with a map `b` to `P` having the
same image `z` in `T` as `a`, is carried to a map to `U` lying over `b`. -/
def pointMove (z : Z ⟶ T) (a : Z ⟶ (D.obj PUnit.unit).left) (b : Z ⟶ P)
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z) : Z ⟶ (D.obj PUnit.unit).left :=
  (D.transport.move (i := PUnit.unit) (j := PUnit.unit) (Z := Over.mk z)
    (Over.homMk a (by simpa using ha)) (Over.homMk b hb)).left

/-- The moved map `D.pointMove z a b ha hb` lies over `b`: followed by the structure map of
the datum it is `b`. -/
@[reassoc (attr := simp)]
lemma pointMove_hom (z : Z ⟶ T) (a : Z ⟶ (D.obj PUnit.unit).left) (b : Z ⟶ P)
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z) :
    D.pointMove z a b ha hb ≫ (D.obj PUnit.unit).hom = b :=
  congrArg CommaMorphism.left (D.transport.move_base (i := PUnit.unit) (j := PUnit.unit)
    (Z := Over.mk z) (Over.homMk a (by simpa using ha)) (Over.homMk b hb))

/-- The move operation is compatible with precomposition: precomposing a moved map with
`k : Z' ⟶ Z` is moving the precomposed maps. -/
lemma comp_pointMove {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : Z' ⟶ Z) (z : Z ⟶ T)
    (a : Z ⟶ (D.obj PUnit.unit).left) (b : Z ⟶ P)
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z) :
    k ≫ D.pointMove z a b ha hb =
      D.pointMove (k ≫ z) (k ≫ a) (k ≫ b) (by simp [ha]) (by simp [hb]) := by
  have h := D.transport.comp_move (i := PUnit.unit) (j := PUnit.unit)
    (Over.homMk k rfl : Over.mk (k ≫ z) ⟶ Over.mk z)
    (Over.homMk a (by simpa using ha)) (Over.homMk b hb)
  have e₁ : (Over.homMk k rfl : Over.mk (k ≫ z) ⟶ Over.mk z) ≫
      (Over.homMk a (by simpa using ha) : Over.mk z ⟶ (Over.map p).obj (D.obj PUnit.unit)) =
      (Over.homMk (k ≫ a) (by simp [ha]) :
        Over.mk (k ≫ z) ⟶ (Over.map p).obj (D.obj PUnit.unit)) := by
    ext; simp
  have e₂ : (Over.homMk k rfl : Over.mk (k ≫ z) ⟶ Over.mk z) ≫
      (Over.homMk b hb : Over.mk z ⟶ Over.mk p) =
        (Over.homMk (k ≫ b) (by simp [hb]) : Over.mk (k ≫ z) ⟶ Over.mk p) := by
    ext; simp
  rw [e₁, e₂] at h
  exact congrArg CommaMorphism.left h

/-- Moving a map `a` to the point `a ≫ (D.obj PUnit.unit).hom` it already lies over gives
back `a`. -/
lemma pointMove_self (z : Z ⟶ T) (a : Z ⟶ (D.obj PUnit.unit).left)
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) :
    D.pointMove z a (a ≫ (D.obj PUnit.unit).hom) ha (by simpa using ha) = a := by
  have h := D.transport.move_self (i := PUnit.unit) (Z := Over.mk z)
    (Over.homMk a (by simpa using ha))
  have e : (Over.homMk a (by simpa using ha) : Over.mk z ⟶ (Over.map p).obj (D.obj PUnit.unit)) ≫
      structureMap p (D.obj PUnit.unit) =
      (Over.homMk (a ≫ (D.obj PUnit.unit).hom) (by simpa using ha) : Over.mk z ⟶ Over.mk p) := by
    ext; simp
  rw [e] at h
  exact congrArg CommaMorphism.left h

/-- Moving a map first over `b` and then over `c` is the same as moving it over `c`
directly. -/
lemma pointMove_pointMove (z : Z ⟶ T) (a : Z ⟶ (D.obj PUnit.unit).left) (b c : Z ⟶ P)
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z) (hc : c ≫ p = z) :
    D.pointMove z (D.pointMove z a b ha hb) c (by rw [pointMove_hom_assoc, hb]) hc =
      D.pointMove z a c ha hc := by
  have h := D.transport.move_comp (i := PUnit.unit) (j := PUnit.unit) (k := PUnit.unit)
    (Z := Over.mk z) (Over.homMk a (by simpa using ha)) (Over.homMk b hb) (Over.homMk c hc)
  have e : D.transport.move (i := PUnit.unit) (j := PUnit.unit) (Z := Over.mk z)
      (Over.homMk a (by simpa using ha)) (Over.homMk b hb) =
      (Over.homMk (D.pointMove z a b ha hb) (by simp [hb]) :
        Over.mk z ⟶ (Over.map p).obj (D.obj PUnit.unit)) := by
    ext; rfl
  rw [e] at h
  exact congrArg CommaMorphism.left h

/-- The move operation respects equalities of its three map arguments; the compatibility
proofs are transported along them. -/
lemma pointMove_congr {z z' : Z ⟶ T} {a a' : Z ⟶ (D.obj PUnit.unit).left} {b b' : Z ⟶ P}
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z) (hz : z = z') (haa : a = a')
    (hbb : b = b') :
    D.pointMove z a b ha hb =
      D.pointMove z' a' b' (by rw [← haa, ← hz, ha]) (by rw [← hbb, ← hz, hb]) := by
  subst hz haa hbb
  rfl

/-- Moving a map `a` over any `b` equal to `a ≫ (D.obj PUnit.unit).hom` gives back `a`. -/
lemma pointMove_eq_self (z : Z ⟶ T) (a : Z ⟶ (D.obj PUnit.unit).left) (b : Z ⟶ P)
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z)
    (hab : b = a ≫ (D.obj PUnit.unit).hom) : D.pointMove z a b ha hb = a := by
  subst hab
  exact D.pointMove_self z a ha

/-- Precomposing a moved map with `k` is moving the maps `a'`, `b'` that are the precompositions
of `a`, `b` with `k`, over any `z'` equal to the precomposition of `z`. -/
private lemma comp_pointMove_eq {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (k : Z' ⟶ Z)
    {z : Z ⟶ T} {a : Z ⟶ (D.obj PUnit.unit).left} {b : Z ⟶ P}
    (ha : a ≫ (D.obj PUnit.unit).hom ≫ p = z) (hb : b ≫ p = z) {z' : Z' ⟶ T}
    {a' : Z' ⟶ (D.obj PUnit.unit).left} {b' : Z' ⟶ P} (ha' : a' ≫ (D.obj PUnit.unit).hom ≫ p = z')
    (hb' : b' ≫ p = z') (hz : k ≫ z = z') (hka : k ≫ a = a') (hkb : k ≫ b = b') :
    k ≫ D.pointMove z a b ha hb = D.pointMove z' a' b' ha' hb' := by
  subst hz hka hkb
  exact D.comp_pointMove k z a b ha hb

end Move

section Sites

/-- The inverse of the composition comparison of base change, followed by the first projection,
is the iterated first projection. -/
private lemma pullbackComp_inv_app_left_fst {C : Type*} [Category C] [HasPullbacks C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (A : Over Z) :
    ((Over.pullbackComp f g).inv.app A).left ≫ pullback.fst A.hom (f ≫ g) =
      pullback.fst ((Over.pullback g).obj A).hom f ≫ pullback.fst A.hom g := by
  rw [← Over.pullbackComp_left_fst_fst f g A, ← Over.comp_left_assoc, Iso.inv_hom_id_app,
    Over.id_left, Category.id_comp]

variable (B S hS) in
/-- The composition comparisons of the pseudofunctor of spaces-étale sites, followed by the
first projection, are the iterated first projections. -/
lemma spacesEtaleSitePseudofunctor_mapComp'_inv_app_fst
    {a b c : LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c)
    (h : φ ≫ ψ = χ) (M : SpacesEtale B S hS a.as.unop) :
    (((spacesEtaleSitePseudofunctor B S hS).mapComp' φ ψ χ h).inv.toNatTrans.app M).hom.left ≫
        pullback.fst M.obj.hom χ.as.unop =
      pullback.fst ((Over.pullback φ.as.unop).obj M.obj).hom ψ.as.unop ≫
        pullback.fst M.obj.hom φ.as.unop := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact pullbackComp_inv_app_left_fst _ _ _

variable (B S hS) in
/-- The composition comparisons of the pseudofunctor of spaces-étale sites, followed by the
iterated first projection, are the first projection. -/
lemma spacesEtaleSitePseudofunctor_mapComp'_hom_app_fst
    {a b c : LocallyDiscrete (AlgebraicSpaces B S hS)ᵒᵖ} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c)
    (h : φ ≫ ψ = χ) (M : SpacesEtale B S hS a.as.unop) :
    (((spacesEtaleSitePseudofunctor B S hS).mapComp' φ ψ χ h).hom.toNatTrans.app M).hom.left ≫
        pullback.fst ((Over.pullback φ.as.unop).obj M.obj).hom ψ.as.unop ≫
          pullback.fst M.obj.hom φ.as.unop =
      pullback.fst M.obj.hom χ.as.unop := by
  subst h
  rw [Pseudofunctor.mapComp'_eq_mapComp]
  exact Over.pullbackComp_left_fst_fst _ _ _

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y}
  (D : HomDescentData.{u, 0} f.hom Y.property X.property)
  (hD : IsEtale B S hS (D.obj PUnit.unit).hom)

/-- The underlying space of a descent datum relative to `f : X ⟶ Y` whose structure map is
étale, as an object of the spaces-étale site of `X`. -/
abbrev etaleObj : SpacesEtale B S hS X :=
  ⟨Over.mk (ObjectProperty.homMk (D.obj PUnit.unit).hom :
    (⟨(D.obj PUnit.unit).left, D.obj_isAlgebraicSpace PUnit.unit⟩ : AlgebraicSpaces B S hS) ⟶
      X), hD⟩

/-- The first projection of a base change of `etaleObj`, followed by the structure map, is the
second projection followed by the morphism base changed along. -/
lemma etaleObj_fst_hom {Y' : AlgebraicSpaces B S hS} (g : Y' ⟶ X) :
    (pullback.fst (etaleObj D hD).obj.hom g).hom ≫ (D.obj PUnit.unit).hom =
      (pullback.snd (etaleObj D hD).obj.hom g).hom ≫ g.hom := by
  simpa using congrArg (fun k => k.hom)
    (pullback.condition (f := (etaleObj D hD).obj.hom) (g := g))

/-- The gluing morphism of the descent datum `toSpacesEtaleDescentData` at a test space `Y'` with
two maps `f₁, f₂` to `X` agreeing over `Y`, on underlying spaces: the point of `f₁^* U` is moved
to the point of `U` over its image under `f₂`. -/
def etaleMove {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X) (h₁ : f₁ ≫ f = q)
    (h₂ : f₂ ≫ f = q) :
    (pullback (etaleObj D hD).obj.hom f₁).obj ⟶ (D.obj PUnit.unit).left :=
  D.pointMove ((pullback.snd (etaleObj D hD).obj.hom f₁).hom ≫ q.hom)
    (pullback.fst (etaleObj D hD).obj.hom f₁).hom
    ((pullback.snd (etaleObj D hD).obj.hom f₁).hom ≫ f₂.hom)
    (by rw [reassoc_of% etaleObj_fst_hom D hD f₁, ← h₁]; rfl)
    (by rw [Category.assoc, ← h₂]; rfl)

/-- The gluing morphism of the descent datum `toSpacesEtaleDescentData`, on the fibre products:
the point of `f₁^* U` goes to the moved point of `U` and the same point of `Y'`. -/
def etaleLift {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X) (h₁ : f₁ ≫ f = q)
    (h₂ : f₂ ≫ f = q) :
    pullback (etaleObj D hD).obj.hom f₁ ⟶ pullback (etaleObj D hD).obj.hom f₂ :=
  pullback.lift (ObjectProperty.homMk (etaleMove D hD q f₁ f₂ h₁ h₂) :
      pullback (etaleObj D hD).obj.hom f₁ ⟶ (etaleObj D hD).obj.left)
    (pullback.snd (etaleObj D hD).obj.hom f₁)
    (ObjectProperty.hom_ext _ (by simp [etaleMove]))

/-- The gluing morphism `etaleLift` followed by the first projection is the moved point
`etaleMove`. -/
@[reassoc (attr := simp)]
lemma etaleLift_fst {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X)
    (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) :
    etaleLift D hD q f₁ f₂ h₁ h₂ ≫ pullback.fst (etaleObj D hD).obj.hom f₂ =
      ObjectProperty.homMk (etaleMove D hD q f₁ f₂ h₁ h₂) :=
  pullback.lift_fst _ _ _

/-- The gluing morphism `etaleLift` followed by the second projection is the second
projection: it lies over the test space `Y'`. -/
@[reassoc (attr := simp)]
lemma etaleLift_snd {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X)
    (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) :
    etaleLift D hD q f₁ f₂ h₁ h₂ ≫ pullback.snd (etaleObj D hD).obj.hom f₂ =
      pullback.snd (etaleObj D hD).obj.hom f₁ :=
  pullback.lift_snd _ _ _

/-- The gluing morphism at a pair `(g, g)` of equal maps is the identity. -/
lemma etaleLift_self {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (g : Y' ⟶ X) (hg : g ≫ f = q) :
    etaleLift D hD q g g hg hg = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [etaleLift_fst, Category.id_comp]
    apply ObjectProperty.hom_ext
    rw [ObjectProperty.homMk_hom]
    exact D.pointMove_eq_self _ _ _ _ _ (etaleObj_fst_hom D hD g).symm
  · rw [etaleLift_snd, Category.id_comp]

/-- The gluing morphisms satisfy the cocycle condition: the gluing morphism at `(f₁, f₂)`
followed by the one at `(f₂, f₃)` is the one at `(f₁, f₃)`. -/
lemma etaleLift_comp {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ f₃ : Y' ⟶ X)
    (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) (h₃ : f₃ ≫ f = q) :
    etaleLift D hD q f₁ f₂ h₁ h₂ ≫ etaleLift D hD q f₂ f₃ h₂ h₃ =
      etaleLift D hD q f₁ f₃ h₁ h₃ := by
  apply pullback.hom_ext
  · rw [Category.assoc, etaleLift_fst, etaleLift_fst]
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, etaleMove]
    have e₁ : (etaleLift D hD q f₁ f₂ h₁ h₂).hom ≫
        (pullback.fst (etaleObj D hD).obj.hom f₂).hom = etaleMove D hD q f₁ f₂ h₁ h₂ := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, etaleLift_fst, ObjectProperty.homMk_hom]
    have e₂ : (etaleLift D hD q f₁ f₂ h₁ h₂).hom ≫
        (pullback.snd (etaleObj D hD).obj.hom f₂).hom =
          (pullback.snd (etaleObj D hD).obj.hom f₁).hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, etaleLift_snd]
    exact (D.comp_pointMove_eq _ _ _ _ _ (by rw [reassoc_of% e₂]) e₁
      (by rw [reassoc_of% e₂])).trans (D.pointMove_pointMove _ _ _ _ _ _ _)
  · rw [Category.assoc, etaleLift_snd, etaleLift_snd, etaleLift_snd]

/-- **Base change of the gluing morphisms.** Conjugating the base change along `g : Y'' ⟶ Y'`
of the gluing morphism at `(f₁, f₂)` by any comparisons of the iterated fibre products with the
fibre products along `g ≫ f₁` and `g ≫ f₂` that are compatible with the projections gives the
gluing morphism at `(g ≫ f₁, g ≫ f₂)`. -/
lemma etaleLift_pull {Y'' Y' : AlgebraicSpaces B S hS} (g : Y'' ⟶ Y') (q : Y' ⟶ Y)
    (f₁ f₂ : Y' ⟶ X) (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q)
    (c₁ : pullback (etaleObj D hD).obj.hom (g ≫ f₁) ⟶
      pullback (pullback.snd (etaleObj D hD).obj.hom f₁) g)
    (hc₁ : c₁ ≫ pullback.fst _ g ≫ pullback.fst (etaleObj D hD).obj.hom f₁ =
      pullback.fst (etaleObj D hD).obj.hom (g ≫ f₁))
    (hc₁' : c₁ ≫ pullback.snd _ g = pullback.snd (etaleObj D hD).obj.hom (g ≫ f₁))
    (c₂ : pullback (pullback.snd (etaleObj D hD).obj.hom f₂) g ⟶
      pullback (etaleObj D hD).obj.hom (g ≫ f₂))
    (hc₂ : c₂ ≫ pullback.fst (etaleObj D hD).obj.hom (g ≫ f₂) =
      pullback.fst _ g ≫ pullback.fst (etaleObj D hD).obj.hom f₂)
    (hc₂' : c₂ ≫ pullback.snd (etaleObj D hD).obj.hom (g ≫ f₂) = pullback.snd _ g) :
    c₁ ≫ pullback.lift (pullback.fst _ g ≫ etaleLift D hD q f₁ f₂ h₁ h₂) (pullback.snd _ g)
        (by rw [Category.assoc, etaleLift_snd, pullback.condition]) ≫ c₂ =
      etaleLift D hD (g ≫ q) (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, h₁])
        (by rw [Category.assoc, h₂]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, hc₂, pullback.lift_fst_assoc, Category.assoc,
      etaleLift_fst, etaleLift_fst]
    apply ObjectProperty.hom_ext
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, etaleMove]
    have e₁ : c₁.hom ≫ (pullback.fst _ g).hom ≫ (pullback.fst (etaleObj D hD).obj.hom f₁).hom =
        (pullback.fst (etaleObj D hD).obj.hom (g ≫ f₁)).hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
        hc₁]
    have e₂ : c₁.hom ≫ (pullback.fst _ g).hom ≫ (pullback.snd (etaleObj D hD).obj.hom f₁).hom =
        (pullback.snd (etaleObj D hD).obj.hom (g ≫ f₁)).hom ≫ g.hom := by
      rw [← ObjectProperty.FullSubcategory.comp_hom, ← ObjectProperty.FullSubcategory.comp_hom,
        pullback.condition, reassoc_of% hc₁', ObjectProperty.FullSubcategory.comp_hom]
    rw [← Category.assoc]
    exact D.comp_pointMove_eq _ _ _ _ _ (by rw [Category.assoc, reassoc_of% e₂])
      (by rw [Category.assoc, e₁]) (by rw [Category.assoc, reassoc_of% e₂])
  · rw [Category.assoc, Category.assoc, hc₂', pullback.lift_snd, hc₁', etaleLift_snd]

/-- The gluing morphism of the descent datum `toSpacesEtaleDescentData`. -/
def etaleHom {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X) (h₁ : f₁ ≫ f = q)
    (h₂ : f₂ ≫ f = q) :
    ((spacesEtaleSitePseudofunctor B S hS).map f₁.op.toLoc).toFunctor.obj (etaleObj D hD) ⟶
      ((spacesEtaleSitePseudofunctor B S hS).map f₂.op.toLoc).toFunctor.obj (etaleObj D hD) :=
  ObjectProperty.homMk (Over.homMk (etaleLift D hD q f₁ f₂ h₁ h₂)
    (etaleLift_snd D hD q f₁ f₂ h₁ h₂))

/-- The morphism of underlying spaces of `etaleHom` is `etaleLift`. -/
lemma etaleHom_hom_left {Y' : AlgebraicSpaces B S hS} (q : Y' ⟶ Y) (f₁ f₂ : Y' ⟶ X)
    (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) :
    (etaleHom D hD q f₁ f₂ h₁ h₂).hom.left = etaleLift D hD q f₁ f₂ h₁ h₂ :=
  rfl

/-- The gluing morphisms of `toSpacesEtaleDescentData` are compatible with base change. -/
lemma pullHom_etaleHom {Y'' Y' : AlgebraicSpaces B S hS} (g : Y'' ⟶ Y') (q : Y' ⟶ Y)
    (f₁ f₂ : Y' ⟶ X) (h₁ : f₁ ≫ f = q) (h₂ : f₂ ≫ f = q) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := spacesEtaleSitePseudofunctor B S hS)
        (etaleHom D hD q f₁ f₂ h₁ h₂) g (g ≫ f₁) (g ≫ f₂) rfl rfl =
      etaleHom D hD (g ≫ q) (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, h₁])
        (by rw [Category.assoc, h₂]) := by
  refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
  let c₁ := (((spacesEtaleSitePseudofunctor B S hS).mapComp' f₁.op.toLoc g.op.toLoc
    (g ≫ f₁).op.toLoc rfl).hom.toNatTrans.app (etaleObj D hD)).hom
  let c₂ := (((spacesEtaleSitePseudofunctor B S hS).mapComp' f₂.op.toLoc g.op.toLoc
    (g ≫ f₂).op.toLoc rfl).inv.toNatTrans.app (etaleObj D hD)).hom
  exact etaleLift_pull D hD g q f₁ f₂ h₁ h₂ c₁.left
    (spacesEtaleSitePseudofunctor_mapComp'_hom_app_fst B S hS _ _ _ _ _) (Over.w c₁) c₂.left
    (spacesEtaleSitePseudofunctor_mapComp'_inv_app_fst B S hS _ _ _ _ _) (Over.w c₂)

/-- **An étale descent datum of algebraic spaces is a descent datum of spaces-étale sites.**
For a descent datum `(U/X, φ)` relative to `f : X ⟶ Y` with `U` étale over `X`, the object `U`
of the spaces-étale site of `X`, together with the gluing morphisms
`AlgebraicGeometry.Space.Descent.HomDescentData.etaleHom` obtained from `φ` over every test
space with two maps to `X` agreeing over `Y`, is a descent datum for the pseudofunctor of
spaces-étale sites relative to `f`. -/
def toSpacesEtaleDescentData :
    (spacesEtaleSitePseudofunctor B S hS).DescentData (fun _ : Unit ↦ f) where
  obj _ := etaleObj D hD
  hom _ q _ _ f₁ f₂ h₁ h₂ := etaleHom D hD q f₁ f₂ h₁ h₂
  pullHom_hom _ _ g q q' hq _ _ f₁ f₂ h₁ h₂ gf₁ gf₂ hgf₁ hgf₂ := by
    subst hq hgf₁ hgf₂
    exact pullHom_etaleHom D hD g q f₁ f₂ h₁ h₂
  hom_self _ q _ g hg :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (etaleLift_self D hD q g hg))
  hom_comp _ q _ _ _ f₁ f₂ f₃ h₁ h₂ h₃ :=
    ObjectProperty.hom_ext _ (Over.OverMorphism.ext (etaleLift_comp D hD q f₁ f₂ f₃ h₁ h₂ h₃))

end Sites

end HomDescentData

end AlgebraicGeometry.Space.Descent

end
