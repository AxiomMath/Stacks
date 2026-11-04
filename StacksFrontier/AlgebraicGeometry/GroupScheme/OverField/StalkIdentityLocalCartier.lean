module

public import StacksFrontier.AlgebraicGeometry.Pullback.StalkTensorTwoSided
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentityComponent
public import StacksFrontier.RingTheory.LocalRing.CounitalComulReduced

/-!
# The comultiplication at the identity of a group scheme is counital

Let `G` be a group scheme over a field `k`, with identity point `e` and local ring
`R = 𝒪_{G, e}`.  The local ring of `G ×_k G` at `(e, e)` is a localization of `R ⊗[k] R` at the
kernel of `ε ⊗ ε`, where `ε : R → k` is evaluation at the unit section; the multiplication of
`G` induces `Δ : R → 𝒪_{G ×_k G, (e, e)}`, and the sections `g ↦ (e, g)` and `g ↦ (g, e)` induce
`π₁, π₂ : 𝒪_{G ×_k G, (e, e)} → R` with `π₁ ∘ Δ = π₂ ∘ Δ = id` and
`π₁ (a ⊗ b) = ε(a) b`, `π₂ (a ⊗ b) = a ε(b)`.  This is the input of the local Cartier theorem
`nilradical_eq_bot_of_counital_of_fg`.

## Main results

* `AlgebraicGeometry.exists_counital_stalk_identity`: the data above.
* `AlgebraicGeometry.isReduced_stalk_identity_of_fg_nilradical`: in characteristic zero, if the
  nilradical of `𝒪_{G, e}` is finitely generated then `𝒪_{G, e}` is reduced.

## Implementation notes

The points `pr₁ (e, e)`, `μ (e, e)` and so on are equal to `e` only propositionally, so maps on
local rings are taken along a stated equality of points (`Scheme.Hom.stalkMapOfEq`), which
composes and depends only on the morphism (`Scheme.Hom.stalkMapOfEq_comp`,
`Scheme.Hom.stalkMapOfEq_congr`).  The localization statement at `(pr₁ w, pr₂ w)`
(`AlgebraicGeometry.exists_isLocalization_atPrime_stalk_pullback_tensorProduct`) is transported
to `R ⊗[k] R` by substituting the equalities of points
(`AlgebraicGeometry.exists_tensor_stalk_transport`).  The construction is split into one
declaration per map and per identity between maps, so that each is elaborated on its own.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The map on local rings induced by a morphism `g : Y ⟶ Z` at a point `y`, with target point
`z = g y` given up to a stated equality. -/
noncomputable def Scheme.Hom.stalkMapOfEq {Y Z : Scheme.{u}} (g : Y ⟶ Z) (y : Y) (z : Z)
    (h : g y = z) : Z.presheaf.stalk z ⟶ Y.presheaf.stalk y :=
  (Z.presheaf.stalkCongr (.of_eq h.symm)).hom ≫ g.stalkMap y

/-- The identification of the stalks at two inseparable points is the identity when the points
are equal. -/
lemma stalkCongr_hom_self {X : Scheme.{u}} {x : X} (e : Inseparable x x) :
    (X.presheaf.stalkCongr e).hom = 𝟙 _ := by
  rw [TopCat.Presheaf.stalkCongr_hom]
  exact TopCat.Presheaf.stalkSpecializes_refl _ _

namespace Scheme.Hom

/-- Maps on local rings along equalities of points compose. -/
lemma stalkMapOfEq_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (g' : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (h : g x = y) (h' : g' y = z) (h'' : (g ≫ g') x = z) :
    (g ≫ g').stalkMapOfEq x z h'' = g'.stalkMapOfEq y z h' ≫ g.stalkMapOfEq x y h := by
  subst h h'
  have e : ∀ e : Inseparable (g' (g x)) ((g ≫ g') x),
      (Z.presheaf.stalkCongr e).hom = 𝟙 (Z.presheaf.stalk (g' (g x))) :=
    fun _ => TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [stalkMapOfEq, stalkMap_comp, stalkCongr_hom_self, Category.id_comp, e]
  exact Category.id_comp (obj := CommRingCat) _

/-- The map on local rings along an equality of points depends only on the morphism. -/
lemma stalkMapOfEq_congr {Y Z : Scheme.{u}} {g g' : Y ⟶ Z} (hg : g = g') (y : Y) (z : Z)
    (h : g y = z) (h' : g' y = z) : g.stalkMapOfEq y z h = g'.stalkMapOfEq y z h' := by
  subst hg
  rfl

/-- The identity induces the identity on local rings. -/
@[simp]
lemma stalkMapOfEq_id {Y : Scheme.{u}} (y : Y) (h : (𝟙 Y : Y ⟶ Y) y = y) :
    (𝟙 Y : Y ⟶ Y).stalkMapOfEq y y h = 𝟙 _ := by
  have e : ∀ e : Inseparable y ((𝟙 Y : Y ⟶ Y) y),
      (Y.presheaf.stalkCongr e).hom = 𝟙 (Y.presheaf.stalk y) :=
    fun _ => TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [stalkMapOfEq, stalkMap_id, e]
  exact Category.id_comp (obj := CommRingCat) _

/-- The map on local rings is compatible with the germs of global sections. -/
@[reassoc]
lemma germ_stalkMapOfEq {Y Z : Scheme.{u}} (g : Y ⟶ Z) (y : Y) (z : Z) (h : g y = z) :
    Z.presheaf.germ ⊤ z trivial ≫ g.stalkMapOfEq y z h =
      g.appTop ≫ Y.presheaf.germ ⊤ y trivial := by
  subst h
  rw [stalkMapOfEq, stalkCongr_hom_self, Category.id_comp]
  exact g.germ_stalkMap ⊤ y trivial

end Scheme.Hom

/-- A ring map out of a tensor product is the product of its restrictions to the two factors. -/
lemma ringHom_tensorProduct_tmul {k A B T : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Semiring T] [Algebra k A] [Algebra k B] (φ : A ⊗[k] B →+* T) (a : A) (b : B) :
    φ (a ⊗ₜ b) = φ.comp Algebra.TensorProduct.includeLeftRingHom a *
      φ.comp Algebra.TensorProduct.includeRight.toRingHom b := by
  simp [← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- A localization at a prime is one at any equal prime. -/
lemma isLocalization_atPrime_of_eq {T S : Type*} [CommRing T] [CommRing S] [Algebra T S]
    {I J : Ideal T} [I.IsPrime] [J.IsPrime] (h : I = J) (H : IsLocalization.AtPrime S I) :
    IsLocalization.AtPrime S J := by
  subst h
  exact H

variable (k : Type u) [Field k]

/-- The `k`-algebra structure on a local ring of a scheme over `Spec k`, through the structure
morphism. -/
noncomputable abbrev germAlgebra {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- A ring map out of a tensor product of two local rings of a scheme over `Spec k`, exhibiting
its target as a localization at a prime, may be moved along equalities of the two points. -/
lemma exists_tensor_stalk_transport {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    {S : Type u} [CommRing S] [IsLocalRing S] (x₁ x₂ y₁ y₂ : X) (h₁ : x₁ = y₁) (h₂ : x₂ = y₂)
    (ψ : letI := germAlgebra k f x₁; letI := germAlgebra k f x₂
      X.presheaf.stalk x₁ ⊗[k] X.presheaf.stalk x₂ →+* S)
    (hloc : letI := germAlgebra k f x₁; letI := germAlgebra k f x₂; letI := ψ.toAlgebra
      IsLocalization.AtPrime S (Ideal.comap ψ (IsLocalRing.maximalIdeal S))) :
    letI := germAlgebra k f x₁; letI := germAlgebra k f x₂
    letI := germAlgebra k f y₁; letI := germAlgebra k f y₂
    ∃ ψ' : X.presheaf.stalk y₁ ⊗[k] X.presheaf.stalk y₂ →+* S,
      (∀ a b, ψ' (a ⊗ₜ b) =
        (ψ.comp Algebra.TensorProduct.includeLeftRingHom)
            ((X.presheaf.stalkCongr (.of_eq h₁.symm)).hom.hom a) *
          (ψ.comp Algebra.TensorProduct.includeRight.toRingHom)
            ((X.presheaf.stalkCongr (.of_eq h₂.symm)).hom.hom b)) ∧
      (letI := ψ'.toAlgebra;
        IsLocalization.AtPrime S (Ideal.comap ψ' (IsLocalRing.maximalIdeal S))) := by
  subst h₁ h₂
  let := germAlgebra k f x₁
  let := germAlgebra k f x₂
  refine ⟨ψ, fun a b => ?_, hloc⟩
  rw [stalkCongr_hom_self, stalkCongr_hom_self]
  exact ringHom_tensorProduct_tmul ψ a b

/-- The map from `k` to the local ring of `Spec k` at its point is an isomorphism. -/
lemma isIso_ΓSpecIso_inv_germ (pt : Spec (CommRingCat.of k)) :
    IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ pt trivial) := by
  have : Subsingleton (Spec (.of k)) := by
    show Subsingleton (PrimeSpectrum k)
    infer_instance
  obtain rfl : pt = IsLocalRing.closedPoint (CommRingCat.of k) := Subsingleton.elim _ _
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv, Iso.inv_hom_id_assoc]
  infer_instance

/-- The point of `Spec k`. -/
noncomputable def basePoint : Spec (CommRingCat.of k) := default

/-- Every point of `Spec k` is its point `basePoint k`. -/
lemma eq_basePoint (x : Spec (CommRingCat.of k)) : x = basePoint k := by
  have : Subsingleton (Spec (.of k)) := by
    show Subsingleton (PrimeSpectrum k)
    infer_instance
  exact Subsingleton.elim _ _

/-- The identification of `k` with the local ring of `Spec k` at its point. -/
noncomputable def baseGerm : CommRingCat.of k ⟶ (Spec (.of k)).presheaf.stalk (basePoint k) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (basePoint k) trivial

/-- The identification `baseGerm k` of `k` with the local ring of `Spec k` is an isomorphism. -/
instance : IsIso (baseGerm k) := isIso_ΓSpecIso_inv_germ k _

variable (G : Grp (Over (Spec (CommRingCat.of k))))

/-- The `k`-algebra structure on the local ring of a group scheme over `k` at its identity point,
through the structure morphism. -/
noncomputable abbrev stalkIdentityAlgebra :
    Algebra k (G.X.left.presheaf.stalk (identityPoint k G)) :=
  germAlgebra k G.X.hom (identityPoint k G)

/-- The structure map of the local ring at the identity, as a morphism. -/
noncomputable abbrev stalkStructureMap :
    CommRingCat.of k ⟶ G.X.left.presheaf.stalk (identityPoint k G) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ G.X.hom.appTop ≫
    G.X.left.presheaf.germ ⊤ (identityPoint k G) trivial

/-- The algebra map of `stalkIdentityAlgebra` is the structure map `stalkStructureMap`. -/
lemma algebraMap_stalkIdentityAlgebra :
    letI := stalkIdentityAlgebra k G
    algebraMap k (G.X.left.presheaf.stalk (identityPoint k G)) = (stalkStructureMap k G).hom :=
  rfl

/-- The unit section sends the point of `Spec k` to the identity point. -/
lemma unit_basePoint : η[G.X].left (basePoint k) = identityPoint k G := rfl

/-- The structure morphism sends every point of `G` to the point of `Spec k`. -/
lemma structure_apply (x : G.X.left) : G.X.hom x = basePoint k := eq_basePoint k _

/-- Evaluation at the unit section, on local rings. -/
noncomputable def stalkCounitMap :
    G.X.left.presheaf.stalk (identityPoint k G) ⟶ (Spec (.of k)).presheaf.stalk (basePoint k) :=
  η[G.X].left.stalkMapOfEq _ _ (unit_basePoint k G)

/-- The structure map followed by evaluation at the unit section is the identification
`baseGerm k` of `k` with the local ring of `Spec k`. -/
lemma stalkStructureMap_stalkCounitMap :
    stalkStructureMap k G ≫ stalkCounitMap k G = baseGerm k := by
  have hηf : η[G.X].left ≫ G.X.hom = 𝟙 _ := Over.w η[G.X]
  rw [stalkCounitMap, Category.assoc, Category.assoc, Scheme.Hom.germ_stalkMapOfEq,
    ← Scheme.Hom.comp_appTop_assoc, hηf, Scheme.Hom.id_appTop]
  exact congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ ·) (Category.id_comp _)

/-- The structure morphism on local rings at the identity is `stalkStructureMap`, read through
the identification `baseGerm k`. -/
lemma structure_stalkMapOfEq :
    G.X.hom.stalkMapOfEq (identityPoint k G) (basePoint k) (structure_apply k G _) =
      inv (baseGerm k) ≫ stalkStructureMap k G := by
  rw [IsIso.eq_inv_comp, baseGerm, Category.assoc, Scheme.Hom.germ_stalkMapOfEq]

/-- The point `(e, e)` of `G ×_k G`, as a section over `Spec k`. -/
noncomputable def identityPair : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ G.X ⊗ G.X :=
  lift η[G.X] η[G.X]

/-- The point `(e, e)` of `G ×_k G`. -/
noncomputable def identityPairPoint : ((pullback G.X.hom G.X.hom : Scheme.{u}) : Type u) :=
  (identityPair k G).left (basePoint k)

/-- The section `identityPair` sends the point of `Spec k` to `(e, e)`. -/
lemma identityPair_basePoint :
    (identityPair k G).left (basePoint k) = identityPairPoint k G := rfl

/-- The first coordinate of the section `(e, e)` is the unit section. -/
lemma identityPair_fst : (identityPair k G).left ≫ pullback.fst G.X.hom G.X.hom = η[G.X].left :=
  congrArg CommaMorphism.left (lift_fst η[G.X] η[G.X])

/-- The second coordinate of the section `(e, e)` is the unit section. -/
lemma identityPair_snd : (identityPair k G).left ≫ pullback.snd G.X.hom G.X.hom = η[G.X].left :=
  congrArg CommaMorphism.left (lift_snd η[G.X] η[G.X])

/-- The multiplication sends the section `(e, e)` to the unit section. -/
lemma identityPair_mul : (identityPair k G).left ≫ μ[G.X].left = η[G.X].left := by
  have := lift_comp_one_left (𝟙 (𝟙_ (Over (Spec (CommRingCat.of k))))) η[G.X]
  rw [Category.id_comp] at this
  exact congrArg CommaMorphism.left this

/-- The first projection sends `(e, e)` to `e`. -/
lemma fst_identityPairPoint :
    pullback.fst G.X.hom G.X.hom (identityPairPoint k G) = identityPoint k G := by
  show ((identityPair k G).left ≫ pullback.fst G.X.hom G.X.hom) (basePoint k) = _
  rw [identityPair_fst]
  rfl

/-- The second projection sends `(e, e)` to `e`. -/
lemma snd_identityPairPoint :
    pullback.snd G.X.hom G.X.hom (identityPairPoint k G) = identityPoint k G := by
  show ((identityPair k G).left ≫ pullback.snd G.X.hom G.X.hom) (basePoint k) = _
  rw [identityPair_snd]
  rfl

/-- The multiplication sends `(e, e)` to `e`. -/
lemma mul_identityPairPoint : μ[G.X].left (identityPairPoint k G) = identityPoint k G := by
  show ((identityPair k G).left ≫ μ[G.X].left) (basePoint k) = _
  rw [identityPair_mul]
  rfl

/-- The section `g ↦ (e, g)` of `G ×_k G`. -/
noncomputable def leftSection : G.X ⟶ G.X ⊗ G.X := lift (toUnit G.X ≫ η[G.X]) (𝟙 G.X)

/-- The section `g ↦ (g, e)` of `G ×_k G`. -/
noncomputable def rightSection : G.X ⟶ G.X ⊗ G.X := lift (𝟙 G.X) (toUnit G.X ≫ η[G.X])

/-- The unit section followed by the constant map to the unit is the unit section. -/
lemma unit_toUnit_unit : η[G.X] ≫ toUnit G.X ≫ η[G.X] = η[G.X] := by
  rw [← Category.assoc, toUnit_unique (η[G.X] ≫ toUnit G.X) (𝟙 _), Category.id_comp]

/-- The section `g ↦ (e, g)` sends `e` to `(e, e)`. -/
lemma leftSection_identityPoint :
    (leftSection k G).left (identityPoint k G) = identityPairPoint k G := by
  show (η[G.X] ≫ leftSection k G).left (basePoint k) = (identityPair k G).left (basePoint k)
  rw [leftSection, comp_lift, unit_toUnit_unit, Category.comp_id]
  rfl

/-- The section `g ↦ (g, e)` sends `e` to `(e, e)`. -/
lemma rightSection_identityPoint :
    (rightSection k G).left (identityPoint k G) = identityPairPoint k G := by
  show (η[G.X] ≫ rightSection k G).left (basePoint k) = (identityPair k G).left (basePoint k)
  rw [rightSection, comp_lift, unit_toUnit_unit, Category.comp_id]
  rfl

/-- The section `g ↦ (e, g)` followed by the multiplication is the identity. -/
lemma leftSection_mul : (leftSection k G).left ≫ μ[G.X].left = 𝟙 _ :=
  congrArg CommaMorphism.left (lift_comp_one_left (toUnit G.X) (𝟙 G.X))

/-- The section `g ↦ (g, e)` followed by the multiplication is the identity. -/
lemma rightSection_mul : (rightSection k G).left ≫ μ[G.X].left = 𝟙 _ :=
  congrArg CommaMorphism.left (lift_comp_one_right (𝟙 G.X) (toUnit G.X))

/-- The first coordinate of the section `g ↦ (e, g)` is the constant map to `e`. -/
lemma leftSection_fst :
    (leftSection k G).left ≫ pullback.fst G.X.hom G.X.hom = G.X.hom ≫ η[G.X].left :=
  congrArg CommaMorphism.left (lift_fst (toUnit G.X ≫ η[G.X]) (𝟙 G.X))

/-- The second coordinate of the section `g ↦ (e, g)` is the identity. -/
lemma leftSection_snd : (leftSection k G).left ≫ pullback.snd G.X.hom G.X.hom = 𝟙 _ :=
  congrArg CommaMorphism.left (lift_snd (toUnit G.X ≫ η[G.X]) (𝟙 G.X))

/-- The first coordinate of the section `g ↦ (g, e)` is the identity. -/
lemma rightSection_fst : (rightSection k G).left ≫ pullback.fst G.X.hom G.X.hom = 𝟙 _ :=
  congrArg CommaMorphism.left (lift_fst (𝟙 G.X) (toUnit G.X ≫ η[G.X]))

/-- The second coordinate of the section `g ↦ (g, e)` is the constant map to `e`. -/
lemma rightSection_snd :
    (rightSection k G).left ≫ pullback.snd G.X.hom G.X.hom = G.X.hom ≫ η[G.X].left :=
  congrArg CommaMorphism.left (lift_snd (𝟙 G.X) (toUnit G.X ≫ η[G.X]))

/-- The local ring of `G ×_k G` at `(e, e)`. -/
noncomputable abbrev stalkPair : CommRingCat :=
  (pullback G.X.hom G.X.hom : Scheme.{u}).presheaf.stalk (identityPairPoint k G)

/-- The first projection on local rings at `(e, e)`. -/
noncomputable abbrev stalkFst : G.X.left.presheaf.stalk (identityPoint k G) ⟶ stalkPair k G :=
  (pullback.fst G.X.hom G.X.hom).stalkMapOfEq _ _ (fst_identityPairPoint k G)

/-- The second projection on local rings at `(e, e)`. -/
noncomputable abbrev stalkSnd : G.X.left.presheaf.stalk (identityPoint k G) ⟶ stalkPair k G :=
  (pullback.snd G.X.hom G.X.hom).stalkMapOfEq _ _ (snd_identityPairPoint k G)

/-- The multiplication on local rings at `(e, e)`. -/
noncomputable abbrev stalkComul : G.X.left.presheaf.stalk (identityPoint k G) ⟶ stalkPair k G :=
  μ[G.X].left.stalkMapOfEq _ _ (mul_identityPairPoint k G)

/-- The section `g ↦ (e, g)` on local rings. -/
noncomputable abbrev stalkLeftProj : stalkPair k G ⟶ G.X.left.presheaf.stalk (identityPoint k G) :=
  (leftSection k G).left.stalkMapOfEq _ _ (leftSection_identityPoint k G)

/-- The section `g ↦ (g, e)` on local rings. -/
noncomputable abbrev stalkRightProj :
    stalkPair k G ⟶ G.X.left.presheaf.stalk (identityPoint k G) :=
  (rightSection k G).left.stalkMapOfEq _ _ (rightSection_identityPoint k G)

/-- Evaluation at `(e, e)`, on local rings. -/
noncomputable abbrev stalkPairCounitMap :
    stalkPair k G ⟶ (Spec (.of k)).presheaf.stalk (basePoint k) :=
  (identityPair k G).left.stalkMapOfEq (basePoint k) (identityPairPoint k G)
    (identityPair_basePoint k G)

/-- Maps on local rings along equalities of points compose, when the composite is identified with
a third morphism. -/
private theorem stalkMapOfEq_comp_of_comp_eq {X Y Z : Scheme.{u}} {g : X ⟶ Y} {g' : Y ⟶ Z}
    {g'' : X ⟶ Z} (hg : g ≫ g' = g'') {x : X} {y : Y} {z : Z} {h : g x = y} {h' : g' y = z}
    {h'' : g'' x = z} :
    g'.stalkMapOfEq y z h' ≫ g.stalkMapOfEq x y h = g''.stalkMapOfEq x z h'' := by
  subst hg
  exact (Scheme.Hom.stalkMapOfEq_comp g g' x y z h h' h'').symm

/-- The first projection followed by evaluation at `(e, e)` is evaluation at `e`. -/
lemma stalkFst_pairCounit : stalkFst k G ≫ stalkPairCounitMap k G = stalkCounitMap k G :=
  stalkMapOfEq_comp_of_comp_eq (identityPair_fst k G)

/-- The second projection followed by evaluation at `(e, e)` is evaluation at `e`. -/
lemma stalkSnd_pairCounit : stalkSnd k G ≫ stalkPairCounitMap k G = stalkCounitMap k G :=
  stalkMapOfEq_comp_of_comp_eq (identityPair_snd k G)

/-- The constant map to `e` induces on local rings at `e` the evaluation at `e` followed by
the structure map. -/
lemma structure_unit_stalkMapOfEq (h : (G.X.hom ≫ η[G.X].left) (identityPoint k G) =
      identityPoint k G) :
    (G.X.hom ≫ η[G.X].left).stalkMapOfEq _ _ h =
      stalkCounitMap k G ≫ inv (baseGerm k) ≫ stalkStructureMap k G := by
  rw [Scheme.Hom.stalkMapOfEq_comp _ _ _ (basePoint k) _ (structure_apply k G _)
    (unit_basePoint k G), structure_stalkMapOfEq]
  rfl

/-- The identity of `G` induces the identity on the local ring at `e`. -/
lemma id_stalkMapOfEq (h : (𝟙 G.X.left : G.X.left ⟶ G.X.left) (identityPoint k G) =
      identityPoint k G) :
    (𝟙 G.X.left : G.X.left ⟶ G.X.left).stalkMapOfEq _ _ h = 𝟙 _ :=
  Scheme.Hom.stalkMapOfEq_id _ h

/-- The first projection followed by the section `g ↦ (e, g)` is evaluation at `e` followed by
the structure map. -/
lemma stalkFst_leftProj : stalkFst k G ≫ stalkLeftProj k G =
    stalkCounitMap k G ≫ inv (baseGerm k) ≫ stalkStructureMap k G := by
  refine (stalkMapOfEq_comp_of_comp_eq (leftSection_fst k G)).trans
    (structure_unit_stalkMapOfEq k G ?_)
  rw [Scheme.Hom.comp_apply, structure_apply]
  rfl

/-- The second projection followed by the section `g ↦ (e, g)` is the identity. -/
lemma stalkSnd_leftProj : stalkSnd k G ≫ stalkLeftProj k G = 𝟙 _ := by
  refine (stalkMapOfEq_comp_of_comp_eq (leftSection_snd k G)).trans (id_stalkMapOfEq k G rfl)

/-- The first projection followed by the section `g ↦ (g, e)` is the identity. -/
lemma stalkFst_rightProj : stalkFst k G ≫ stalkRightProj k G = 𝟙 _ := by
  refine (stalkMapOfEq_comp_of_comp_eq (rightSection_fst k G)).trans (id_stalkMapOfEq k G rfl)

/-- The second projection followed by the section `g ↦ (g, e)` is evaluation at `e` followed by
the structure map. -/
lemma stalkSnd_rightProj : stalkSnd k G ≫ stalkRightProj k G =
    stalkCounitMap k G ≫ inv (baseGerm k) ≫ stalkStructureMap k G := by
  refine (stalkMapOfEq_comp_of_comp_eq (rightSection_snd k G)).trans
    (structure_unit_stalkMapOfEq k G ?_)
  rw [Scheme.Hom.comp_apply, structure_apply]
  rfl

/-- The multiplication followed by the section `g ↦ (e, g)` is the identity on local rings. -/
lemma stalkComul_leftProj : stalkComul k G ≫ stalkLeftProj k G = 𝟙 _ := by
  refine (stalkMapOfEq_comp_of_comp_eq (leftSection_mul k G)).trans (id_stalkMapOfEq k G rfl)

/-- The multiplication followed by the section `g ↦ (g, e)` is the identity on local rings. -/
lemma stalkComul_rightProj : stalkComul k G ≫ stalkRightProj k G = 𝟙 _ := by
  refine (stalkMapOfEq_comp_of_comp_eq (rightSection_mul k G)).trans (id_stalkMapOfEq k G rfl)

section Algebra

/- In what follows the `k`-algebra structure on the local ring at the identity is an arbitrary
one agreeing with the structure morphism; `stalkIdentityAlgebra` is one. -/
variable [Algebra k (G.X.left.presheaf.stalk (identityPoint k G))]

/-- **The counit at the identity**: evaluation at the unit section, `𝒪_{G, e} → k`. -/
noncomputable def stalkCounit
    (hR : algebraMap k (G.X.left.presheaf.stalk (identityPoint k G)) =
      (stalkStructureMap k G).hom) :
    G.X.left.presheaf.stalk (identityPoint k G) →ₐ[k] k where
  toRingHom := (stalkCounitMap k G ≫ inv (baseGerm k)).hom
  commutes' c := by
    rw [hR]
    change ((stalkStructureMap k G ≫ stalkCounitMap k G) ≫ inv (baseGerm k)).hom c = c
    rw [stalkStructureMap_stalkCounitMap, IsIso.hom_inv_id]
    rfl

variable (hR : algebraMap k (G.X.left.presheaf.stalk (identityPoint k G)) =
  (stalkStructureMap k G).hom)

/-- The counit at the identity is evaluation at the unit section. -/
lemma stalkCounit_apply (a : G.X.left.presheaf.stalk (identityPoint k G)) :
    stalkCounit k G hR a = (stalkCounitMap k G ≫ inv (baseGerm k)).hom a := rfl

include hR in
/-- The counit at the identity followed by the algebra map is evaluation at `e` followed by the
structure map. -/
lemma algebraMap_stalkCounit (a : G.X.left.presheaf.stalk (identityPoint k G)) :
    algebraMap k _ (stalkCounit k G hR a) =
      (stalkCounitMap k G ≫ inv (baseGerm k) ≫ stalkStructureMap k G).hom a := by
  rw [hR]
  rfl

include hR in
/-- The local ring of `G ×_k G` at `(e, e)` is a localization of `R ⊗[k] R`, through the two
projections. -/
lemma exists_stalkPair_tensor :
    ∃ ψ : G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
        G.X.left.presheaf.stalk (identityPoint k G) →+* stalkPair k G,
      (∀ a b, ψ (a ⊗ₜ b) = (stalkFst k G).hom a * (stalkSnd k G).hom b) ∧
      (letI := ψ.toAlgebra;
        IsLocalization.AtPrime (stalkPair k G)
          (Ideal.comap ψ (IsLocalRing.maximalIdeal (stalkPair k G)))) := by
  obtain rfl : ‹Algebra k (G.X.left.presheaf.stalk (identityPoint k G))› =
      stalkIdentityAlgebra k G := Algebra.algebra_ext _ _ fun c => congrArg (· c) hR
  obtain ⟨ψ, hψ₁, hψ₂, hloc⟩ := exists_isLocalization_atPrime_stalk_pullback_tensorProduct k
    G.X.hom G.X.hom (identityPairPoint k G)
  obtain ⟨ψ', hψ', hloc'⟩ := exists_tensor_stalk_transport k G.X.hom _ _ _ _
    (fst_identityPairPoint k G) (snd_identityPairPoint k G) ψ hloc
  refine ⟨ψ', fun a b => ?_, hloc'⟩
  rw [hψ', hψ₁, hψ₂]
  rfl

variable {k G} in
/-- Evaluation at `(e, e)` restricts along `ψ` to `ε ⊗ ε` on `R ⊗[k] R`. -/
lemma pairCounit_comp (ψ : G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
      G.X.left.presheaf.stalk (identityPoint k G) →+* stalkPair k G)
    (hψ : ∀ a b, ψ (a ⊗ₜ b) = (stalkFst k G).hom a * (stalkSnd k G).hom b)
    (t : G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
      G.X.left.presheaf.stalk (identityPoint k G)) :
    (stalkPairCounitMap k G ≫ inv (baseGerm k)).hom (ψ t) =
      Algebra.TensorProduct.lift (stalkCounit k G hR) (stalkCounit k G hR)
        (fun _ _ => .all _ _) t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [hψ, map_mul, Algebra.TensorProduct.lift_tmul, stalkCounit_apply, stalkCounit_apply,
      ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
      ← Category.assoc, ← Category.assoc, stalkFst_pairCounit, stalkSnd_pairCounit]
  | add s t hs ht => rw [map_add, map_add, hs, ht, map_add]

variable {k G} in
/-- The maximal ideal of the local ring at `(e, e)` pulls back along `ψ` to the kernel of
`ε ⊗ ε`. -/
lemma comap_maximalIdeal_eq_counitTensorKer
    (ψ : G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
      G.X.left.presheaf.stalk (identityPoint k G) →+* stalkPair k G)
    (hψ : ∀ a b, ψ (a ⊗ₜ b) = (stalkFst k G).hom a * (stalkSnd k G).hom b) :
    Ideal.comap ψ (IsLocalRing.maximalIdeal (stalkPair k G)) =
      counitTensorKer (stalkCounit k G hR) := by
  have hker : RingHom.ker (stalkPairCounitMap k G ≫ inv (baseGerm k)).hom =
      IsLocalRing.maximalIdeal (stalkPair k G) := by
    refine IsLocalRing.ker_eq_maximalIdeal _ fun c =>
      ⟨ψ (algebraMap k (G.X.left.presheaf.stalk (identityPoint k G)) c ⊗ₜ 1), ?_⟩
    rw [pairCounit_comp hR ψ hψ, Algebra.TensorProduct.lift_tmul, AlgHom.commutes, map_one,
      _root_.mul_one]
    rfl
  ext t
  rw [Ideal.mem_comap, ← hker, RingHom.mem_ker, counitTensorKer, RingHom.mem_ker,
    pairCounit_comp hR ψ hψ]
  rfl

variable {k G} in
/-- The section `g ↦ (e, g)` sends `a ⊗ b` to `ε(a) b`. -/
lemma stalkLeftProj_tmul (ψ : G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
      G.X.left.presheaf.stalk (identityPoint k G) →+* stalkPair k G)
    (hψ : ∀ a b, ψ (a ⊗ₜ b) = (stalkFst k G).hom a * (stalkSnd k G).hom b)
    (a b : G.X.left.presheaf.stalk (identityPoint k G)) :
    (stalkLeftProj k G).hom (ψ (a ⊗ₜ b)) = algebraMap k _ (stalkCounit k G hR a) * b := by
  rw [hψ, map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, stalkFst_leftProj, stalkSnd_leftProj, algebraMap_stalkCounit k G hR]
  rfl

variable {k G} in
/-- The section `g ↦ (g, e)` sends `a ⊗ b` to `a ε(b)`. -/
lemma stalkRightProj_tmul (ψ : G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
      G.X.left.presheaf.stalk (identityPoint k G) →+* stalkPair k G)
    (hψ : ∀ a b, ψ (a ⊗ₜ b) = (stalkFst k G).hom a * (stalkSnd k G).hom b)
    (a b : G.X.left.presheaf.stalk (identityPoint k G)) :
    (stalkRightProj k G).hom (ψ (a ⊗ₜ b)) = a * algebraMap k _ (stalkCounit k G hR b) := by
  rw [hψ, map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, stalkFst_rightProj, stalkSnd_rightProj, algebraMap_stalkCounit k G hR]
  rfl

omit [Algebra k (G.X.left.presheaf.stalk (identityPoint k G))] in
/-- The section `g ↦ (e, g)` is a left inverse of the comultiplication on local rings. -/
lemma stalkLeftProj_stalkComul (r : G.X.left.presheaf.stalk (identityPoint k G)) :
    (stalkLeftProj k G).hom ((stalkComul k G).hom r) = r := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, stalkComul_leftProj]
  rfl

omit [Algebra k (G.X.left.presheaf.stalk (identityPoint k G))] in
/-- The section `g ↦ (g, e)` is a left inverse of the comultiplication on local rings. -/
lemma stalkRightProj_stalkComul (r : G.X.left.presheaf.stalk (identityPoint k G)) :
    (stalkRightProj k G).hom ((stalkComul k G).hom r) = r := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, stalkComul_rightProj]
  rfl

end Algebra

/-- **The comultiplication at the identity of a group scheme over a field is counital.**  With
`R` the local ring at the identity and `ε : R → k` evaluation at the unit section, there are a
localization `S` of `R ⊗[k] R` at the kernel of `ε ⊗ ε` (the local ring of `G ×_k G` at
`(e, e)`), a ring map `Δ : R → S` (induced by the multiplication) and ring maps `π₁, π₂ : S → R`
(induced by `g ↦ (e, g)` and `g ↦ (g, e)`) with `π₁ (a ⊗ b) = ε(a) b`, `π₂ (a ⊗ b) = a ε(b)` and
`π₁ ∘ Δ = π₂ ∘ Δ = id`. -/
theorem exists_counital_stalk_identity :
    letI := stalkIdentityAlgebra k G
    ∃ (ε : G.X.left.presheaf.stalk (identityPoint k G) →ₐ[k] k) (S : Type u) (_ : CommRing S)
      (_ : Algebra (G.X.left.presheaf.stalk (identityPoint k G) ⊗[k]
        G.X.left.presheaf.stalk (identityPoint k G)) S),
      IsLocalization.AtPrime S (counitTensorKer ε) ∧
      ∃ (Δ : G.X.left.presheaf.stalk (identityPoint k G) →+* S)
        (π₁ π₂ : S →+* G.X.left.presheaf.stalk (identityPoint k G)),
        (∀ a b, π₁ (algebraMap _ S (a ⊗ₜ[k] b)) = algebraMap k _ (ε a) * b) ∧
        (∀ a b, π₂ (algebraMap _ S (a ⊗ₜ[k] b)) = a * algebraMap k _ (ε b)) ∧
        (∀ r, π₁ (Δ r) = r) ∧ (∀ r, π₂ (Δ r) = r) := by
  let := stalkIdentityAlgebra k G
  have hR := algebraMap_stalkIdentityAlgebra k G
  obtain ⟨ψ, hψ, hloc⟩ := exists_stalkPair_tensor k G hR
  let := ψ.toAlgebra
  refine ⟨stalkCounit k G hR, stalkPair k G, inferInstance, ψ.toAlgebra, ?_,
    (stalkComul k G).hom, (stalkLeftProj k G).hom, (stalkRightProj k G).hom,
    stalkLeftProj_tmul hR ψ hψ, stalkRightProj_tmul hR ψ hψ, stalkLeftProj_stalkComul k G,
    stalkRightProj_stalkComul k G⟩
  exact isLocalization_atPrime_of_eq (comap_maximalIdeal_eq_counitTensorKer hR ψ hψ) hloc

/-- **The local ring of a group scheme over a field of characteristic zero at its identity is
reduced as soon as its nilradical is finitely generated.**  The comultiplication on the local
ring at the identity is counital (`AlgebraicGeometry.exists_counital_stalk_identity`), so this is
the local Cartier theorem `nilradical_eq_bot_of_counital_of_fg`. -/
theorem isReduced_stalk_identity_of_fg_nilradical [CharZero k]
    (hN : (nilradical (G.X.left.presheaf.stalk (identityPoint k G))).FG) :
    _root_.IsReduced (G.X.left.presheaf.stalk (identityPoint k G)) := by
  let := stalkIdentityAlgebra k G
  obtain ⟨ε, S, _, _, _, Δ, π₁, π₂, hπ₁, hπ₂, h₁, h₂⟩ := exists_counital_stalk_identity k G
  exact nilradical_eq_bot_iff.mp
    (nilradical_eq_bot_of_counital_of_fg ε Δ π₁ π₂ hπ₁ hπ₂ h₁ h₂ hN)

end AlgebraicGeometry
