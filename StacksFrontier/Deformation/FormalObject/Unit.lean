module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.FiberedCategory.HomLift
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory

/-!
# The unit map to the category of formal objects

The unit of the completion: a category cofibered in groupoids maps to its
category of formal objects.

## Main definitions

* `Restriction` is the strict restriction of a category over complete local
  algebras to Artinian local algebras.
* `AdicPushforwardChoice` records the pushforwards used to form the unit.
* `adicPushforwardChoice` chooses these pushforwards from the
  cofibered structure.
* `CompletionUnit` packages the unit functor and its canonical formulas.

## Main results

* `completionUnit` constructs the unit morphism to formal objects.

## Implementation notes

An Artinian local algebra is regarded as a complete local algebra using its canonical
inclusion `artinianToComplete`.  Restriction is represented by a strict pullback
category.
The formulas in `CompletionUnit` say that the level objects are the chosen pushforwards,
that its transition arrows are induced by their universal property, and that the maps on
morphisms are the compatible maps induced by the same universal property.  The pushforward
choice is constructed from the cofibered hypothesis, so the unit does not require an
externally supplied choice.

## References

* [Stacks Project, Tag 06HA](https://stacks.math.columbia.edu/tag/06HA)
-/

@[expose] public section

namespace Deformation

/-! ### The unit map to the category of formal objects -/

section
open CategoryTheory
open IsLocalRing
universe u v w uG vG uC vC


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]



/-- An arrow whose opposite is strongly cartesian for `p.op` is strongly cocartesian for `p`. -/
public theorem stronglyCocartesian_of_op
    {G : Type uG} [Category.{vG} G]
    {C : Type uC} [Category.{vC} C]
    (p : G ⥤ C) {R S : C} {X Y : G} (f : R ⟶ S) (φ : X ⟶ Y)
    (h : p.op.IsStronglyCartesian f.op φ.op) : p.IsStronglyCocartesian f φ := by
  let : p.op.IsStronglyCartesian f.op φ.op := h
  have hφ : p.IsHomLift f φ := isHomLift_unop p f.op φ.op
  let : p.IsHomLift f φ := hφ
  refine ⟨?_⟩
  intro Z g ψ hψ
  let : p.IsHomLift (f ≫ g) ψ := hψ
  have hψop : p.op.IsHomLift (g.op ≫ f.op) ψ.op := by
    simpa only [← op_comp] using isHomLift_op p (f ≫ g) ψ
  obtain ⟨χ, ⟨hχ, hχcomp⟩, huniq⟩ :=
    h.universal_property' g.op ψ.op
  refine ⟨χ.unop, ⟨?_, ?_⟩, ?_⟩
  · exact isHomLift_unop p g.op χ (inst := hχ)
  · simpa using congrArg Quiver.Hom.unop hχcomp
  · intro χ' hχ'
    have hχ'op : p.op.IsHomLift g.op χ'.op := isHomLift_op p g χ' (inst := hχ'.1)
    have hχ'comp : χ'.op ≫ φ.op = ψ.op := by
      simpa only [op_comp] using congrArg Quiver.Hom.op hχ'.2
    simpa using congrArg Quiver.Hom.unop (huniq χ'.op ⟨hχ'op, hχ'comp⟩)

/-- The quotient map `R ⟶ R / m_R^(n+1)` from a complete local algebra to its `n`-th adic
truncation, viewed as a complete local algebra. -/
public noncomputable def adicQuotientMap
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    R ⟶ artinianToComplete.obj ((AdicTruncation.functor n).obj R) := by
  let I := AdicTruncation.ideal R n
  have hI : I < ⊤ :=
    (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt (maximalIdeal.isMaximal R).lt_top
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let q := Ideal.Quotient.mkₐ Λ I
  letI : IsLocalHom q := ⟨(IsLocalHom.of_surjective q.toRingHom
    Ideal.Quotient.mk_surjective).map_nonunit⟩
  exact {
    hom := q
    isLocal := ⟨(IsLocalHom.of_surjective q.toRingHom
      Ideal.Quotient.mk_surjective).map_nonunit⟩
    residue_comm := AdicTruncation.residueEquiv_residue_mk R n
  }

/-- A chosen pushforward of `X` along the adic quotient map `p X ⟶ p X / m^(n+1)`, given by the
cofibered structure: its target together with the arrow from `X`. -/
public noncomputable def chosenAdicLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (X : G) (n : ℕ) : Σ Y : G, X ⟶ Y := by
  classical
  let h := hp.exists_lift (adicQuotientMap (p.obj X) n).op (Opposite.op X) rfl
  exact ⟨(Classical.choose h).unop,
    (Classical.choose (Classical.choose_spec h)).unop⟩

/-- The arrow of `chosenAdicLift` lies over the adic quotient map. -/
public theorem chosenAdicLift_isHomLift
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (X : G) (n : ℕ) :
    p.IsHomLift (adicQuotientMap (p.obj X) n) (chosenAdicLift p hp X n).2 := by
  classical
  let h := hp.exists_lift (adicQuotientMap (p.obj X) n).op (Opposite.op X) rfl
  exact isHomLift_unop p _ _
    (inst := Classical.choose_spec (Classical.choose_spec h))

/-- The strict restriction to Artinian local algebras of a category over complete local
algebras.  The equality records that the displayed Artinian algebra is exactly the base of
the original object. -/
public structure Restriction
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k) where
  /-- The underlying object of the original cofibered category. -/
  obj : G
  /-- Its Artinian base algebra. -/
  base : ArtinianLocalAlgCat.{u, v, w} Λ k
  /-- The original base is the image of the Artinian base. -/
  obj_eq : p.obj obj = artinianToComplete.obj base

namespace Restriction

variable {G : Type uG} [Category.{vG} G]
  {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}

/-- A morphism in the restriction is a morphism upstairs and a morphism of Artinian bases
whose images commute after transport along the displayed equalities. -/
public structure Hom (X Y : Restriction p) where
  /-- The underlying morphism upstairs. -/
  obj : X.obj ⟶ Y.obj
  /-- The morphism between Artinian bases. -/
  base : X.base ⟶ Y.base
  /-- Compatibility with the projections to complete local algebras. -/
  comm : eqToHom X.obj_eq ≫ artinianToComplete.map base =
    p.map obj ≫ eqToHom Y.obj_eq

/-- Morphisms in the restriction are equal when their morphisms upstairs and their base
morphisms are equal. -/
@[ext]
public theorem Hom.ext {X Y : Restriction p} {f g : Hom X Y}
    (hobj : f.obj = g.obj) (hbase : f.base = g.base) : f = g := by
  cases f
  cases g
  cases hobj
  cases hbase
  rfl

/-- Identity morphism in the restriction. -/
public def Hom.id (X : Restriction p) : Hom X X where
  obj := 𝟙 X.obj
  base := 𝟙 X.base
  comm := by simp

/-- Composition of morphisms in the restriction. -/
public def Hom.comp {X Y Z : Restriction p} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  obj := f.obj ≫ g.obj
  base := f.base ≫ g.base
  comm := by
    rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, f.comm,
      Category.assoc, g.comm, ← Category.assoc]

/-- The category structure on the restriction, with componentwise identities and
composition. -/
public instance : Category (Restriction p) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (Category.id_comp _) (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Projection of the restricted category to Artinian local algebras. -/
@[implicit_reducible]
public def projection : Restriction p ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k where
  obj X := X.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

end Restriction

/-- The chosen pushforward of `X` to the `n`-th adic truncation of its base, as an object of
the restriction. -/
public noncomputable def chosenAdicLevel
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) (X : G) (n : ℕ) : Restriction p := by
  letI := chosenAdicLift_isHomLift p hp X n
  exact ⟨(chosenAdicLift p hp X n).1, (AdicTruncation.functor n).obj (p.obj X),
    IsHomLift.codomain_eq p (adicQuotientMap (p.obj X) n) (chosenAdicLift p hp X n).2⟩

/-- A simultaneous choice of the pushforwards of every object along all its adic quotient
maps.  The equation on `baseMap` ensures that the displayed map is precisely
`R → R / m_R^(n+1)`, rather than merely a map with the same target. -/
public structure AdicPushforwardChoice
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k) where
  /-- The chosen pushforward, viewed in the restricted category. -/
  level : G → ℕ → Restriction p
  /-- The adic quotient map in the base category. -/
  baseMap : (X : G) → (n : ℕ) →
    p.obj X ⟶ artinianToComplete.obj
      ((AdicTruncation.functor n).obj (p.obj X))
  /-- The base map is the usual quotient homomorphism. -/
  baseMap_hom : ∀ X n,
    (baseMap X n).hom = Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal (p.obj X) n)
  /-- The chosen arrow to the pushforward. -/
  inclusion : ∀ X n, X ⟶ (level X n).obj
  /-- The target really lies over the specified truncation and the chosen arrow lies over
  the quotient map. -/
  inclusion_lift : ∀ X n, p.IsHomLift (baseMap X n) (inclusion X n)
  /-- The chosen arrow has the universal property of a pushforward. -/
  cocartesian : ∀ X n, p.IsStronglyCocartesian (baseMap X n) (inclusion X n)

/-- Choose the pushforwards along all adic quotient maps from the cofibered structure.
These choices are auxiliary: different choices give canonically isomorphic unit morphisms. -/
public noncomputable def adicPushforwardChoice
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) : AdicPushforwardChoice p := by
  refine ⟨chosenAdicLevel p hp, (fun X n => adicQuotientMap (p.obj X) n), fun _ _ => rfl,
    fun X n => (chosenAdicLift p hp X n).2, chosenAdicLift_isHomLift p hp, fun X n => ?_⟩
  let : p.op.IsHomLift (adicQuotientMap (p.obj X) n).op
      (Opposite.op (chosenAdicLift p hp X n).2) :=
    isHomLift_op p (adicQuotientMap (p.obj X) n) (chosenAdicLift p hp X n).2
      (inst := chosenAdicLift_isHomLift p hp X n)
  exact stronglyCocartesian_of_op p (adicQuotientMap (p.obj X) n)
    (chosenAdicLift p hp X n).2
    (hp.isStronglyCartesian_homLift (adicQuotientMap (p.obj X) n).op
      (Opposite.op (chosenAdicLift p hp X n).2))

/-- The unit functor together with the formulas characterizing it on objects and arrows. -/
public structure CompletionUnit
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : AdicPushforwardChoice p) where
  /-- The functor from the cofibered category to formal objects of its restriction. -/
  functor : G ⥤ FormalObject (Restriction.projection (p := p))
  /-- The unit is a morphism of categories over the base. -/
  comp_projection : functor ⋙ FormalObject.projection = p
  /-- Its level `n` is the chosen pushforward to the `n`-th adic quotient. -/
  level : ∀ X n, (functor.obj X).level n = P.level X n
  /-- The transition map is the unique induced map between two successive pushforwards. -/
  transition : ∀ X n,
    P.inclusion X (n + 1) ≫
        eqToHom (congrArg Restriction.obj (level X (n + 1)).symm) ≫
        ((functor.obj X).transition n).obj ≫
        eqToHom (congrArg Restriction.obj (level X n)) =
      P.inclusion X n
  /-- On a morphism it is the compatible map between the chosen towers. -/
  map : ∀ {X Y} (f : X ⟶ Y) (n : ℕ),
    P.inclusion X n ≫ eqToHom (congrArg Restriction.obj (level X n).symm) ≫
        ((functor.map f).app n).obj ≫
        eqToHom (congrArg Restriction.obj (level Y n)) =
      f ≫ P.inclusion Y n

/-- The adic quotient maps are compatible with the transition maps between successive adic
truncations. -/
public theorem baseMap_transition
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p) (X : G) (n : ℕ) :
    P.baseMap X (n + 1) ≫ artinianToComplete.map
      (AdicTruncation.transition (p.obj X) n) = P.baseMap X n := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro r
  rw [CompleteLocalAlgCat.comp_hom, P.baseMap_hom, P.baseMap_hom]
  rfl

/-- The adic quotient maps are natural with respect to morphisms of the cofibered category. -/
public theorem baseMap_naturality
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p) {X Y : G} (f : X ⟶ Y) (n : ℕ) :
    P.baseMap X n ≫ artinianToComplete.map
      ((AdicTruncation.functor n).map (p.map f)) =
      p.map f ≫ P.baseMap Y n := by
  apply CompleteLocalAlgCat.Hom.ext
  apply AlgHom.ext
  intro r
  rw [CompleteLocalAlgCat.comp_hom, CompleteLocalAlgCat.comp_hom,
    P.baseMap_hom, P.baseMap_hom]
  let I := AdicTruncation.ideal (p.obj X) n
  let J := AdicTruncation.ideal (p.obj Y) n
  have hIJ : I ≤ J.comap (p.map f).hom := by
    let : IsLocalHom (p.map f).hom.toRingHom := (p.map f).isLocal
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le (p.map f).hom.toRingHom) _
  exact congrArg (fun q => q r) (Ideal.quotient_map_comp_mkₐ (J := J) (f := (p.map f).hom) hIJ)

/-- The transition morphism from level `n + 1` to level `n` of the chosen pushforwards of `X`,
induced by the universal property of the pushforward at level `n + 1`. -/
public noncomputable def inducedTransitionHom
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p)
    (hbase : ∀ X n, (P.level X n).base = (AdicTruncation.functor n).obj (p.obj X))
    (X : G) (n : ℕ) :
    Restriction.Hom (P.level X (n + 1)) (P.level X n) := by
  let f := P.baseMap X (n + 1)
  let g := artinianToComplete.map (AdicTruncation.transition (p.obj X) n)
  let hsq : f ≫ g = P.baseMap X n := baseMap_transition P X n
  letI := P.cocartesian X (n + 1)
  letI : p.IsHomLift f (P.inclusion X (n + 1)) := P.inclusion_lift X (n + 1)
  letI : p.IsHomLift (P.baseMap X n) (P.inclusion X n) := P.inclusion_lift X n
  let τ := Functor.IsStronglyCocartesian.map p f (P.inclusion X (n + 1)) hsq.symm
    (P.inclusion X n)
  have hτ : p.IsHomLift g τ :=
    Functor.IsStronglyCocartesian.map_isHomLift p f (P.inclusion X (n + 1)) hsq.symm
      (P.inclusion X n)
  exact {
    obj := τ
    base := eqToHom (hbase X (n + 1)) ≫ AdicTruncation.transition (p.obj X) n ≫
      eqToHom (hbase X n).symm
    comm := by
      have hdom : (P.level X (n + 1)).obj_eq.trans
          (congrArg artinianToComplete.obj (hbase X (n + 1))) =
          IsHomLift.domain_eq p g τ := Subsingleton.elim _ _
      have hcod : (P.level X n).obj_eq.trans
          (congrArg artinianToComplete.obj (hbase X n)) =
          IsHomLift.codomain_eq p g τ := Subsingleton.elim _ _
      rw [IsHomLift.fac' p g τ, ← hdom, ← hcod]
      apply CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro r
      simp [g, eqToHom_map, Functor.map_comp, Category.assoc]
  }

/-- The chosen arrow followed by the map induced by its universal property is the given
arrow. -/
private theorem inclusion_comp_map_eq
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p) (X : G) (n : ℕ)
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} {Z : G}
    {g : artinianToComplete.obj ((AdicTruncation.functor n).obj (p.obj X)) ⟶ R}
    {f' : p.obj X ⟶ R} (hf' : f' = P.baseMap X n ≫ g) (φ' : X ⟶ Z) [p.IsHomLift f' φ']
    [p.IsStronglyCocartesian (P.baseMap X n) (P.inclusion X n)] :
    P.inclusion X n ≫
      Functor.IsStronglyCocartesian.map p (P.baseMap X n) (P.inclusion X n) hf' φ' = φ' :=
  Functor.IsStronglyCocartesian.fac p _ _ hf' φ'

/-- The induced transition morphism factors the level-`n` arrow through the level-`n + 1`
arrow. -/
public theorem inducedTransitionHom_fac
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p)
    (hbase : ∀ X n, (P.level X n).base = (AdicTruncation.functor n).obj (p.obj X))
    (X : G) (n : ℕ) :
    P.inclusion X (n + 1) ≫ (inducedTransitionHom P hbase X n).obj = P.inclusion X n := by
  dsimp [inducedTransitionHom]
  let := P.cocartesian X (n + 1)
  let : p.IsHomLift (P.baseMap X n) (P.inclusion X n) := P.inclusion_lift X n
  exact inclusion_comp_map_eq P X (n + 1) (baseMap_transition P X n).symm _

/-- The morphism between the level-`n` chosen pushforwards of `X` and `Y` induced by
`f : X ⟶ Y` through the universal property of the pushforward of `X`. -/
public noncomputable def inducedMapHom
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p)
    (hbase : ∀ X n, (P.level X n).base = (AdicTruncation.functor n).obj (p.obj X))
    {X Y : G} (f : X ⟶ Y) (n : ℕ) :
    Restriction.Hom (P.level X n) (P.level Y n) := by
  let q := P.baseMap X n
  let g := artinianToComplete.map ((AdicTruncation.functor n).map (p.map f))
  let hsq : q ≫ g = p.map f ≫ P.baseMap Y n := baseMap_naturality P f n
  letI := P.cocartesian X n
  letI : p.IsHomLift (P.baseMap Y n) (P.inclusion Y n) := P.inclusion_lift Y n
  letI : p.IsHomLift (p.map f) f := IsHomLift.map (p := p) f
  have hlift : p.IsHomLift (q ≫ g) (f ≫ P.inclusion Y n) := by
    have hcomp : p.IsHomLift (p.map f ≫ P.baseMap Y n) (f ≫ P.inclusion Y n) :=
      IsHomLift.comp p (p.map f) (P.baseMap Y n) f (P.inclusion Y n)
    exact hsq.symm ▸ hcomp
  let τ := Functor.IsStronglyCocartesian.map p q (P.inclusion X n)
    (g := g) (f' := q ≫ g) rfl
    (f ≫ P.inclusion Y n)
  have hτ : p.IsHomLift g τ :=
    Functor.IsStronglyCocartesian.map_isHomLift p q (P.inclusion X n) (by rfl)
      (f ≫ P.inclusion Y n)
  exact {
    obj := τ
    base := eqToHom (hbase X n) ≫ (AdicTruncation.functor n).map (p.map f) ≫
      eqToHom (hbase Y n).symm
    comm := by
      have hdom : (P.level X n).obj_eq.trans
          (congrArg artinianToComplete.obj (hbase X n)) =
          IsHomLift.domain_eq p g τ := Subsingleton.elim _ _
      have hcod : (P.level Y n).obj_eq.trans
          (congrArg artinianToComplete.obj (hbase Y n)) =
          IsHomLift.codomain_eq p g τ := Subsingleton.elim _ _
      rw [IsHomLift.fac' p g τ, ← hdom, ← hcod]
      apply CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro r
      simp [g, eqToHom_map, Functor.map_comp, Category.assoc]
  }

/-- The induced morphism between chosen pushforwards is compatible with `f` and the chosen
arrows. -/
public theorem inducedMapHom_fac
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p)
    (hbase : ∀ X n, (P.level X n).base = (AdicTruncation.functor n).obj (p.obj X))
    {X Y : G} (f : X ⟶ Y) (n : ℕ) :
    P.inclusion X n ≫ (inducedMapHom P hbase f n).obj = f ≫ P.inclusion Y n := by
  dsimp [inducedMapHom]
  let := P.cocartesian X n
  let : p.IsHomLift (P.baseMap Y n) (P.inclusion Y n) := P.inclusion_lift Y n
  let g := artinianToComplete.map ((AdicTruncation.functor n).map (p.map f))
  have hsq : P.baseMap X n ≫ g = p.map f ≫ P.baseMap Y n := baseMap_naturality P f n
  let : p.IsHomLift (p.map f ≫ P.baseMap Y n) (f ≫ P.inclusion Y n) := inferInstance
  let : p.IsHomLift (P.baseMap X n ≫ g) (f ≫ P.inclusion Y n) := hsq.symm ▸ inferInstance
  exact inclusion_comp_map_eq P X n rfl _

/-- Two morphisms out of a chosen pushforward are equal when they agree after the chosen arrow
and have equal base morphisms. -/
private theorem Restriction.Hom.ext_of_fac
    {G : Type uG} [Category.{vG} G]
    {p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k}
    (P : AdicPushforwardChoice p) {X Y : G} {m n : ℕ}
    (hbase' : ∀ X n, (P.level X n).base = (AdicTruncation.functor n).obj (p.obj X))
    (f g : Restriction.Hom (P.level X m) (P.level Y n))
    (hfac : P.inclusion X m ≫ f.obj = P.inclusion X m ≫ g.obj)
    (hbase : f.base = g.base) : f = g := by
  have hobj : f.obj = g.obj := by
    let : p.IsHomLift (P.baseMap X m) (P.inclusion X m) := P.inclusion_lift X m
    let : p.IsStronglyCocartesian (P.baseMap X m) (P.inclusion X m) := P.cocartesian X m
    let ha : p.obj (P.level X m).obj =
        artinianToComplete.obj ((AdicTruncation.functor m).obj (p.obj X)) :=
      (P.level X m).obj_eq.trans (congrArg artinianToComplete.obj (hbase' X m))
    let gf : artinianToComplete.obj ((AdicTruncation.functor m).obj (p.obj X)) ⟶
        p.obj (P.level Y n).obj :=
      artinianToComplete.map (eqToHom (hbase' X m).symm ≫ f.base) ≫
        eqToHom (P.level Y n).obj_eq.symm
    let gg : artinianToComplete.obj ((AdicTruncation.functor m).obj (p.obj X)) ⟶
        p.obj (P.level Y n).obj :=
      artinianToComplete.map (eqToHom (hbase' X m).symm ≫ g.base) ≫
        eqToHom (P.level Y n).obj_eq.symm
    have hha : eqToHom ha = eqToHom (P.level X m).obj_eq ≫
        artinianToComplete.map (eqToHom (hbase' X m)) := by
      calc
        eqToHom ha = eqToHom ((P.level X m).obj_eq.trans
            (congrArg artinianToComplete.obj (hbase' X m))) := rfl
        _ = eqToHom (P.level X m).obj_eq ≫
            eqToHom (congrArg artinianToComplete.obj (hbase' X m)) :=
          (eqToHom_trans _ _).symm
        _ = eqToHom (P.level X m).obj_eq ≫
            artinianToComplete.map (eqToHom (hbase' X m)) :=
          congrArg (fun t => eqToHom (P.level X m).obj_eq ≫ t)
            (eqToHom_map artinianToComplete (hbase' X m)).symm
    have hlift (a : Restriction.Hom (P.level X m) (P.level Y n)) :
        p.IsHomLift
          (artinianToComplete.map
            (eqToHom (hbase' X m).symm ≫ a.base) ≫
            eqToHom (P.level Y n).obj_eq.symm) a.obj := by
      apply IsHomLift.of_fac' p _ a.obj ha rfl
      dsimp [ha]
      calc
        p.map a.obj = (p.map a.obj ≫ eqToHom (P.level Y n).obj_eq) ≫
            eqToHom (P.level Y n).obj_eq.symm := by simp
        _ = (eqToHom (P.level X m).obj_eq ≫
            artinianToComplete.map a.base) ≫
            eqToHom (P.level Y n).obj_eq.symm := by rw [← a.comm]
        _ = eqToHom ha ≫ _ := by
          rw [hha]
          simp [Functor.map_comp, Category.assoc]
    let : p.IsHomLift gf f.obj := hlift f
    let : p.IsHomLift gg g.obj := hlift g
    have hmap' : (eqToHom (hbase' X m).symm ≫ f.base) =
        (eqToHom (hbase' X m).symm ≫ g.base) := by rw [hbase]
    have hlg' : gf = gg := by simp [gf, gg, hmap']
    let : p.IsHomLift gf g.obj := hlg'.symm ▸ hlift g
    exact Functor.IsStronglyCocartesian.ext p (P.baseMap X m) (P.inclusion X m) gf
      (ψ := f.obj) (ψ' := g.obj) hfac
  exact Restriction.Hom.ext hobj hbase

/-- **Stacks Project, Tag 06HA (unit).** Chosen pushforwards along all adic quotient maps
assemble canonically into a morphism from a category cofibered in groupoids to the category
of formal objects of its restriction.  It sends an object to its tower of chosen
pushforwards, with the induced transition maps. -/
@[stacks 06HA "unit"]
public noncomputable def completionUnit
    {G : Type uG} [Category.{vG} G]
    (p : G ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)
    (hp : IsCofiberedInGroupoids p) :
    CompletionUnit p (adicPushforwardChoice p hp) :=
  by
    let P := adicPushforwardChoice p hp
    have hbase (X : G) (n : ℕ) : (P.level X n).base =
        (AdicTruncation.functor n).obj (p.obj X) := rfl
    let O : G → FormalObject (Restriction.projection (p := p)) := fun X =>
      { base := p.obj X
        level := fun n => P.level X n
        level_eq := fun n => hbase X n
        transition := fun n => inducedTransitionHom P hbase X n
        transition_lift := fun n => by
          have h := IsHomLift.of_fac'
            (p := Restriction.projection (p := p))
            (AdicTruncation.transition (p.obj X) n)
            (inducedTransitionHom P hbase X n)
            (hbase X (n + 1)) (hbase X n) (by
              change eqToHom (hbase X (n + 1)) ≫ AdicTruncation.transition (p.obj X) n ≫
                eqToHom (hbase X n).symm =
                eqToHom (hbase X (n + 1)) ≫
                  AdicTruncation.transition (p.obj X) n ≫ eqToHom (hbase X n).symm
              rfl)
          simpa [AdicTruncation.transitionNat] using h }
    let mapHom : ∀ {X Y : G}, (f : X ⟶ Y) → O X ⟶ O Y :=
      fun {X Y} (f : X ⟶ Y) => by
        refine FormalObject.Hom.mk (base := p.map f)
          (app := fun n => inducedMapHom P hbase f n)
          (app_lift := fun n =>
            IsHomLift.of_fac'
              (p := Restriction.projection (p := p))
              ((AdicTruncation.functor n).map (p.map f))
              (inducedMapHom P hbase f n)
              (hbase X n) (hbase Y n) (by
                change eqToHom (hbase X n) ≫
                  (AdicTruncation.functor n).map (p.map f) ≫
                    eqToHom (hbase Y n).symm = _
                rfl))
          (naturality := by
            intro n
            apply Restriction.Hom.ext_of_fac P hbase
            · change P.inclusion X (n + 1) ≫ (inducedTransitionHom P hbase X n).obj ≫
                (inducedMapHom P hbase f n).obj =
                  P.inclusion X (n + 1) ≫ (inducedMapHom P hbase f (n + 1)).obj ≫
                    (inducedTransitionHom P hbase Y n).obj
              simp only [← Category.assoc, inducedTransitionHom_fac P hbase X n,
                inducedMapHom_fac P hbase f n,
                inducedMapHom_fac P hbase f (n + 1)]
              rw [Category.assoc, inducedTransitionHom_fac P hbase Y n]
            · change (inducedTransitionHom P hbase X n).base ≫
                  (inducedMapHom P hbase f n).base =
                (inducedMapHom P hbase f (n + 1)).base ≫
                  (inducedTransitionHom P hbase Y n).base
              have hnat := (AdicTruncation.transitionNat n).naturality (p.map f)
              have hnatbase : AdicTruncation.transition (p.obj X) n ≫
                  (AdicTruncation.functor n).map (p.map f) =
                (AdicTruncation.functor (n + 1)).map (p.map f) ≫
                  AdicTruncation.transition (p.obj Y) n := by
                simpa only [AdicTruncation.transitionNat] using Eq.symm hnat
              have hnattransport := congrArg (fun t =>
                (eqToHom (hbase X (n + 1)) ≫ t) ≫ eqToHom (hbase Y n).symm) hnatbase
              simpa [hbase, inducedTransitionHom, inducedMapHom, eqToHom_trans,
                eqToHom_refl, Category.assoc] using hnattransport)
    let F : G ⥤ FormalObject (Restriction.projection (p := p)) := {
      obj := O
      map := fun {X Y} f => mapHom f
      map_id := by
        intro X
        apply FormalObject.Hom.ext
        · change p.map (𝟙 X) = 𝟙 (p.obj X)
          simp
        · intro n
          apply Restriction.Hom.ext_of_fac P hbase
          · change P.inclusion X n ≫ (inducedMapHom P hbase (𝟙 X) n).obj =
              P.inclusion X n ≫ (𝟙 (P.level X n).obj)
            simpa using (inducedMapHom_fac P hbase (𝟙 X) n)
          · change (inducedMapHom P hbase (𝟙 X) n).base = 𝟙 (P.level X n).base
            dsimp [inducedMapHom]
            simp [hbase]
      map_comp := by
        intro X Y Z f g
        apply FormalObject.Hom.ext
        · exact p.map_comp f g
        · intro n
          apply Restriction.Hom.ext_of_fac P hbase
          · calc
              P.inclusion X n ≫ (inducedMapHom P hbase (f ≫ g) n).obj =
                  (f ≫ g) ≫ P.inclusion Z n :=
                inducedMapHom_fac P hbase (f ≫ g) n
              _ = f ≫ (g ≫ P.inclusion Z n) := Category.assoc _ _ _
              _ = f ≫ (P.inclusion Y n ≫ (inducedMapHom P hbase g n).obj) := by
                rw [← inducedMapHom_fac P hbase g n]
              _ = (f ≫ P.inclusion Y n) ≫ (inducedMapHom P hbase g n).obj :=
                (Category.assoc _ _ _).symm
              _ = (P.inclusion X n ≫ (inducedMapHom P hbase f n).obj) ≫
                    (inducedMapHom P hbase g n).obj := by
                rw [inducedMapHom_fac P hbase f n]
              _ = P.inclusion X n ≫
                    ((inducedMapHom P hbase f n).obj ≫
                      (inducedMapHom P hbase g n).obj) := Category.assoc _ _ _
              _ = P.inclusion X n ≫ ((mapHom f ≫ mapHom g).app n).obj := by
                rfl
          · change (inducedMapHom P hbase (f ≫ g) n).base =
                ((mapHom f ≫ mapHom g).app n).base
            have hcompBase : ((mapHom f ≫ mapHom g).app n).base =
                ((mapHom f).app n).base ≫ ((mapHom g).app n).base := rfl
            rw [hcompBase]
            dsimp [mapHom, inducedMapHom]
            simp [Functor.map_comp, eqToHom_refl, Category.assoc]
    }
    refine ⟨F, rfl, fun _ _ => rfl, fun X n => ?_, ?_⟩
    · simpa [F, hbase] using inducedTransitionHom_fac P hbase X n
    · intro X Y f n
      simpa [F, hbase] using inducedMapHom_fac P hbase f n

end

end Deformation
