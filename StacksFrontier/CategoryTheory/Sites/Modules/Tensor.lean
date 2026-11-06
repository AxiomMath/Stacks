module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# Tensor products of sheaves of modules on a site

Let `O` be a presheaf of commutative rings on a site `(C, J)`, let `Osharp` be an associated
sheaf of commutative rings, and let `F` and `G` be presheaves of `O`-modules. The tensor
product of two sheaves of modules is obtained by sheafifying the tensor product of the
underlying presheaves of modules, and this construction is compatible with sheafification:
the tensor product of the sheaves associated with `F` and `G` is canonically isomorphic to
the sheaf associated with the presheaf tensor product `F ⊗ G`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.moduleSheafificationUnit` is the unit map from a
  presheaf of modules to the restriction of scalars of its associated sheaf.
* `Stacks.SheafOfModules.Tensor.sheafTensor` is the canonical tensor product of sheaves
  of modules, defined by sheafifying the tensor product of their underlying presheaves.

## Main results

* `PresheafOfModules.sheafificationTensorIso` expresses compatibility of sheafification with
  tensor products in independent module universes.
* `PresheafOfModules.sheafificationTensorIso_hom_unit_tmul` characterizes that isomorphism
  on the images of pure tensors under the generic sheafification units.

## Implementation notes

An associated sheaf of rings is represented by a locally bijective map from the original
presheaf of rings, rather than by a choice of sheafification functor. The compatibility
result is stated as an isomorphism of bifunctors, so naturality in both presheaves of
modules is part of the statement. Its canonicality is pinned down by requiring that its
components carry the sheafification-unit image of the tensor of the two unit images to the
sheafification-unit image of the original pure tensor.

The descent machinery `descent_fiber`, `descent_exists`, `descentFun`,
`descentFun_naturality` and `descentFun_comp` for type-valued presheaves is proved by hand
rather than obtained from `CategoryTheory.MorphismProperty.isLocal.homEquiv`, because the
latter needs `J.WEqualsLocallyBijective (Type w)`, which is available only when the universe
`w` of sections is `max u v`; here it is independent of the universes of the site. The target
sheaf is allowed to take its sections in a universe of its own, so the descended datum is a
family of maps together with its compatibility with restriction rather than a morphism of
presheaves; `descent` and `descent_comp` are the bundled form, available when the source and
target presheaves take sections in the same universe.

Instance search cannot see through `PresheafOfModules.sheafification`, so the local
injectivity and surjectivity of `unitTypes` are supplied as the bridging instances
`isLocallyInjective_unitTypes` and `isLocallySurjective_unitTypes`.

## References

* [Stacks, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe v u w w'

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The underlying map of presheaves of rings of a map to an associated sheaf of commutative
rings. -/
abbrev associatedRingMap {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {Osharp : Sheaf J CommRingCat.{w}} (a : O ⟶ Osharp.obj) :
    O ⋙ forget₂ CommRingCat.{w} RingCat.{w} ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj :=
  Functor.whiskerRight a (forget₂ CommRingCat.{w} RingCat.{w})

/-- The objectwise tensor product gives a monoidal structure on presheaves of modules over
the underlying presheaf of rings of `Osharp`. -/
noncomputable instance monoidalCategoryAssociatedRing
    (Osharp : Sheaf J CommRingCat.{w}) :
    MonoidalCategory (PresheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := Osharp.obj)

variable {O : Cᵒᵖ ⥤ CommRingCat.{w}} {Osharp : Sheaf J CommRingCat.{w}}
  (a : O ⟶ Osharp.obj)
  [Presheaf.IsLocallyInjective J (associatedRingMap J a)]
  [Presheaf.IsLocallySurjective J (associatedRingMap J a)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheafification of presheaves of modules along an associated-sheaf map of rings. -/
noncomputable abbrev moduleSheafification :
    PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⥤
      _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Osharp) :=
  PresheafOfModules.sheafification (associatedRingMap J a)

/-- The unit from a presheaf of modules to the restriction of scalars of its associated
sheaf. -/
noncomputable abbrev moduleSheafificationUnit
    (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :=
  (PresheafOfModules.sheafificationAdjunction (associatedRingMap J a)).unit.app F


section

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

section Descent

variable {P Q : Cᵒᵖ ⥤ Type w} {H : Cᵒᵖ ⥤ Type w'} (f : P ⟶ Q)
  [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f]
  (hH : Presheaf.IsSheaf J H) (b : ∀ X, P.obj X → H.obj X)
  (hb : ∀ {X Y : Cᵒᵖ} (k : X ⟶ Y) (x : P.obj X), b Y (P.map k x) = H.map k (b X x))

include hH hb

omit [Presheaf.IsLocallySurjective J f] in
/-- A map to a sheaf cannot separate two sections that a locally injective map identifies. -/
lemma descent_fiber {U : Cᵒᵖ} (x y : P.obj U)
    (h : f.app U x = f.app U y) : b U x = b U y := by
  apply hH.isSeparated _ _ (Presheaf.equalizerSieve_mem J f x y h)
  intro V g hg
  show H.map g.op (b U x) = H.map g.op (b U y)
  rw [← hb, ← hb]
  exact congrArg (b _) hg

/-- Every section of `Q` has a well-defined image in a sheaf `H`, computed from any local
preimage in `P`. -/
lemma descent_exists (U : Cᵒᵖ) (y : Q.obj U) :
    ∃ z : H.obj U, ∀ {V : Cᵒᵖ} (g : U ⟶ V) (x : P.obj V),
      f.app V x = Q.map g y → H.map g z = b V x := by
  let S := Presheaf.imageSieve f y
  let t : Presieve.FamilyOfElements H S.arrows :=
    fun V g hg ↦ b _ (Presheaf.localPreimage f y g hg)
  have ht : t.Compatible := by
    intro V₁ V₂ W g₁ g₂ p₁ p₂ hp₁ hp₂ he
    dsimp [t]
    rw [← hb, ← hb]
    apply descent_fiber J f hH b hb
    rw [f.naturality_apply, f.naturality_apply,
      Presheaf.app_localPreimage, Presheaf.app_localPreimage,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, he]
  let sh := (isSheaf_iff_isSheaf_of_type J H).mp hH S (Presheaf.imageSieve_mem J f y)
  refine ⟨sh.amalgamate t ht, ?_⟩
  intro V g x hx
  have hg : S g.unop := ⟨x, hx⟩
  exact (sh.valid_glue ht g.unop hg).trans
    (descent_fiber J f hH b hb _ x ((Presheaf.app_localPreimage f y g.unop hg).trans hx.symm))

/-- The section of `H` over `U` obtained by descending `b` along a locally bijective
`f : P ⟶ Q`. The universe of the sections of `H` is unconstrained by that of `P` and `Q`. -/
noncomputable def descentFun (U : Cᵒᵖ) (y : Q.obj U) : H.obj U :=
  (descent_exists J f hH b hb U y).choose

/-- The descended family is compatible with restriction of sections. -/
lemma descentFun_naturality {U V : Cᵒᵖ} (g : U ⟶ V) (y : Q.obj U) :
    descentFun J f hH b hb V (Q.map g y) = H.map g (descentFun J f hH b hb U y) := by
  apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J f (Q.map g y))
  rintro W p ⟨x, hx⟩
  show H.map p.op ((descent_exists J f hH b hb V (Q.map g y)).choose) =
    H.map p.op (H.map g ((descent_exists J f hH b hb U y).choose))
  rw [(descent_exists J f hH b hb V (Q.map g y)).choose_spec p.op x hx,
    ← Functor.map_comp_apply]
  exact ((descent_exists J f hH b hb U y).choose_spec (g ≫ p.op) x
    (by simpa using hx)).symm

/-- The descended family restricts to the original one along `f`. -/
lemma descentFun_comp (U : Cᵒᵖ) (x : P.obj U) :
    descentFun J f hH b hb U (f.app U x) = b U x := by
  simpa [descentFun] using
    (descent_exists J f hH b hb U (f.app U x)).choose_spec (𝟙 U) x (by simp)

end Descent

section DescentHom

variable {P Q H : Cᵒᵖ ⥤ Type w} (f : P ⟶ Q)
  [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallySurjective J f]
  (hH : Presheaf.IsSheaf J H) (b : P ⟶ H)

include hH

/-- The map to a sheaf `H` obtained by descending `b : P ⟶ H` along a locally bijective
`f : P ⟶ Q`. -/
noncomputable def descent : Q ⟶ H where
  app U := ↾fun y ↦ descentFun J f hH (fun X x ↦ b.app X x)
    (fun k x ↦ b.naturality_apply k x) U y
  naturality {U V} g := by
    ext y
    exact descentFun_naturality J f hH (fun X x ↦ b.app X x)
      (fun k x ↦ b.naturality_apply k x) g y

/-- The descended map restricts to the original one along `f`. -/
lemma descent_comp : f ≫ descent J f hH b = b := by
  ext U x
  exact descentFun_comp J f hH (fun X x ↦ b.app X x)
    (fun k x ↦ b.naturality_apply k x) U x

end DescentHom

/-- The objectwise product of two type-valued presheaves. -/
def pairPresheaf (P Q : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w where
  obj U := P.obj U × Q.obj U
  map f := ↾fun x ↦ (P.map f x.1, Q.map f x.2)
  map_id U := by ext x <;> simp
  map_comp f g := by ext x <;> simp

/-- The objectwise product of two maps of type-valued presheaves. -/
def pairMap {P Q P' Q' : Cᵒᵖ ⥤ Type w} (f : P ⟶ P') (g : Q ⟶ Q') :
    pairPresheaf P Q ⟶ pairPresheaf P' Q' where
  app U := ↾fun x ↦ (f.app U x.1, g.app U x.2)
  naturality {U V} k := by
    ext x
    apply Prod.ext
    · exact f.naturality_apply k x.1
    · exact g.naturality_apply k x.2

/-- A product of locally injective maps is locally injective. -/
lemma pairMap_injective {P Q P' Q' : Cᵒᵖ ⥤ Type w} (f : P ⟶ P') (g : Q ⟶ Q')
    [Presheaf.IsLocallyInjective J f] [Presheaf.IsLocallyInjective J g] :
    Presheaf.IsLocallyInjective J (pairMap f g) where
  equalizerSieve_mem {U} x y h := by
    apply J.superset_covering (S := Presheaf.equalizerSieve (F := P) x.1 y.1 ⊓
      Presheaf.equalizerSieve (F := Q) x.2 y.2)
    · intro V k hk
      exact Prod.ext hk.1 hk.2
    · exact J.intersection_covering
        (Presheaf.equalizerSieve_mem J f _ _ (congrArg Prod.fst h))
        (Presheaf.equalizerSieve_mem J g _ _ (congrArg Prod.snd h))

/-- A product of locally surjective maps is locally surjective. -/
lemma pairMap_surjective {P Q P' Q' : Cᵒᵖ ⥤ Type w} (f : P ⟶ P') (g : Q ⟶ Q')
    [Presheaf.IsLocallySurjective J f] [Presheaf.IsLocallySurjective J g] :
    Presheaf.IsLocallySurjective J (pairMap f g) where
  imageSieve_mem {U} x := by
    apply J.superset_covering (S := Presheaf.imageSieve f x.1 ⊓ Presheaf.imageSieve g x.2)
    · rintro V k ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
      exact ⟨(x, y), Prod.ext hx hy⟩
    · exact J.intersection_covering (Presheaf.imageSieve_mem J f _)
        (Presheaf.imageSieve_mem J g _)

end

attribute [local instance] pairMap_injective pairMap_surjective

/-- The underlying type-valued presheaf of sections of a presheaf of modules. -/
noncomputable abbrev moduleTypes {R : Cᵒᵖ ⥤ RingCat.{w}} (F : PresheafOfModules.{w} R) :=
  F.presheaf ⋙ forget AddCommGrpCat.{w}

/-- The sheafification unit of a presheaf of modules, as a map of type-valued presheaves. -/
noncomputable abbrev unitTypes
    (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    moduleTypes F ⟶ moduleTypes ((moduleSheafification J a).obj F).val :=
  Functor.whiskerRight (CategoryTheory.toSheafify J F.presheaf) (forget AddCommGrpCat.{w})

/-- The sheafification unit of a presheaf of modules is locally injective on sections. -/
instance isLocallyInjective_unitTypes
    (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    Presheaf.IsLocallyInjective J (unitTypes J a F) :=
  inferInstanceAs (Presheaf.IsLocallyInjective J
    (Functor.whiskerRight (CategoryTheory.toSheafify J F.presheaf)
      (forget AddCommGrpCat.{w})))

/-- The sheafification unit of a presheaf of modules is locally surjective on sections. -/
instance isLocallySurjective_unitTypes
    (F : PresheafOfModules.{w} (O ⋙ forget₂ CommRingCat.{w} RingCat.{w})) :
    Presheaf.IsLocallySurjective J (unitTypes J a F) :=
  inferInstanceAs (Presheaf.IsLocallySurjective J
    (Functor.whiskerRight (CategoryTheory.toSheafify J F.presheaf)
      (forget AddCommGrpCat.{w})))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The map obtained from the universal property of sheafification agrees with the original
map on the image of the sheafification unit. -/
lemma lift_unit_apply
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    (P : PresheafOfModules.{w} R₀) (N : _root_.SheafOfModules.{w} R)
    (t : P ⟶ (PresheafOfModules.restrictScalars α).obj N.val)
    (U : Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafificationHomEquiv α).symm t).val.app U
      (((PresheafOfModules.sheafificationAdjunction α).unit.app P).app U x) =
      t.app U x :=
  congrArg (fun k ↦ k.app U x)
    ((PresheafOfModules.sheafificationHomEquiv α).apply_symm_apply t)

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- Sheafification of a map of presheaves of modules commutes with the sheafification
units. -/
lemma sheafification_map_unit
    {R₀ : Cᵒᵖ ⥤ RingCat.{w}} {R : Sheaf J RingCat.{w}} (α : R₀ ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    {P Q : PresheafOfModules.{w} R₀} (f : P ⟶ Q) (U : Cᵒᵖ) (x : P.obj U) :
    ((PresheafOfModules.sheafification α).map f).val.app U
      (((PresheafOfModules.sheafificationAdjunction α).unit.app P).app U x) =
    ((PresheafOfModules.sheafificationAdjunction α).unit.app Q).app U (f.app U x) :=
  (congrArg (fun k ↦ k.app U x)
    ((PresheafOfModules.sheafificationAdjunction α).unit.naturality f)).symm

end AlgebraicGeometry.SheafOfModules

add_to_stacks 0GMW PresheafOfModules.sheafificationTensorIso
add_to_stacks 0GMW PresheafOfModules.sheafificationTensorIso_hom_unit_tmul
