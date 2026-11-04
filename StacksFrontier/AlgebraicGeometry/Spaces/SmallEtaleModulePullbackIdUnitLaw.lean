module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdUnitLaw
public import StacksFrontier.CategoryTheory.EqToHomAbsorption

/-!
# The unit law of Stacks 03LU for the inverse image, at a morphism presented as an identity

[Stacks Project, Tag 03LU] attaches to a morphism `f : X ⟶ Y` of algebraic spaces the inverse
image `f^*` of `𝒪`-modules, the comparison
`AlgebraicGeometry.Space.modulePullbackCompIso` of `g^* ∘ f^*` with `(f ≫ g)^*`, and to an
identity the identification `AlgebraicGeometry.Space.modulePullbackIdIso` of `(𝟙 X)^*` with the
identity functor.  This file proves the compatibility of those two data at a pair of identities,
and then at a pair of morphisms which some lemma merely *says* are identities — the shape in
which a consumer meets it, since `AlgebraicGeometry.Space.representedSpaceMap B S hS (𝟙 T)` is
the identity of the represented algebraic space by
`AlgebraicGeometry.Space.representedSpaceMap_id` and not by `rfl`.

The companion for the direct image is
`AlgebraicGeometry.Space.modulePushforwardCompIso_id_id_hom_app` of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardIdUnitLaw.lean`, and it is
what makes this file's first result cheap: that file also proves
`AlgebraicGeometry.Space.modulePushforwardCoherence_modulePullbackIdIso`, which says the unit
datum of the pseudofunctoriality the repository constructs *is* the identification carrying the
03LU tag, so the unit coherence
`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left` becomes a
statement about `AlgebraicGeometry.Space.modulePullbackIdIso` itself.

The Zariski counterpart is recorded here too, for the same consumer: Mathlib states its unit law
as `AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality`, a single equation of natural
transformations with the pseudofunctor's structural transport on the right, and
`AlgebraicGeometry.Scheme.Modules.pullbackComp_id_id_hom_app` is that equation solved for the
component of the composition comparison.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_id_id`: **the unit law of
  [Stacks Project, Tag 03LU] for the inverse image at a pair of identities**, as an equation of
  isomorphisms of functors.
* `AlgebraicGeometry.Space.modulePullbackCompIso_of_eq_id`: the same at a morphism `m` given
  with an equality `m = 𝟙 X`, the transport along that equality appearing in the statement.
* `AlgebraicGeometry.Scheme.Modules.pullbackComp_id_id_hom_app`: the unit law of the Zariski
  inverse image at a pair of identities, read at a module.

## Implementation notes

**Both 03LU statements are made at the level of isomorphisms of functors, and the passage to a
component is left to the consumer.**  This is deliberate, and it is the whole reason the transport
is a declaration of its own.  The same transport carried out one level down — the statement at a
variable `m` with `hid : m = 𝟙 X` read at a module, with the composite padded by the `eqToHom`
that type-correctness then requires, and proved by `subst hid` followed by the component form at
`𝟙 X` — elaborates without complaint and is a **kernel deterministic timeout**.  The padded
*statement* is not the cost: with its proof stubbed out it checks instantly, as does the
already-substituted component form with the padding absorbed by
`CategoryTheory.comp_eqToHom_of_refl`.  It is the `subst` itself, at the component level, that
the kernel cannot afford; at the level of isomorphisms the identical substitution is free, and
the whole file checks in under a second.

**The reflexive transports are absorbed by generic lemmas applied in term position**, not by
`rw` or `simp`: after the substitution the two sides of each transport are definitionally but
not syntactically equal, which is exactly the situation `CategoryTheory.eqToHom_comp_of_refl`
and `CategoryTheory.comp_eqToHom_of_refl` exist for, and
`Stacks.CategoryTheory.trans_eqToIso_of_refl` and
`Stacks.CategoryTheory.eqToIso_of_refl_trans` are their counterparts for isomorphisms.

No `stacks` tag is registered on the generic lemmas.  The two 03LU results are coherences of the
data of that tag, and the tag's own registrations are on
`AlgebraicGeometry.Space.modulePullback`, `AlgebraicGeometry.Space.modulePullbackCompIso` and
`AlgebraicGeometry.Space.modulePullbackIdIso`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

universe u

namespace Stacks.CategoryTheory

open CategoryTheory

/-- **A unit law whiskered on the left and contracted, read at an object.**

Stated at plain variables, where it is free; the geometric instance is an equation between
components of isomorphisms of functors built by sheafification, and reading it there directly is
a kernel deterministic timeout. -/
theorem isoWhiskerLeft_trans_rightUnitor_hom_app {C : Type*} [Category* C] {D : Type*}
    [Category* D] (F : C ⥤ D) {G : D ⥤ D} (e : G ≅ 𝟭 D) (Z : C) :
    (Functor.isoWhiskerLeft F e ≪≫ F.rightUnitor).hom.app Z = e.hom.app (F.obj Z) := by
  simp

/-- **A reflexive `eqToIso` is absorbed on the right of a composite of isomorphisms.**

Applied in term position this also covers an `eqToIso` between two objects that are only
definitionally equal, which is what `CategoryTheory.Iso.trans_refl` cannot match; it is the
counterpart for isomorphisms of `CategoryTheory.comp_eqToHom_of_refl`. -/
theorem trans_eqToIso_of_refl {C : Type*} [Category* C] {A B : C} (e : A ≅ B) (h : B = B) :
    e ≪≫ eqToIso h = e := by
  simp

/-- **A reflexive `eqToIso` is absorbed on the left of a composite of isomorphisms.**

The counterpart for isomorphisms of `CategoryTheory.eqToHom_comp_of_refl`; see
`Stacks.CategoryTheory.trans_eqToIso_of_refl`. -/
theorem eqToIso_of_refl_trans {C : Type*} [Category* C] {A B : C} (h : A = A) (e : A ≅ B) :
    eqToIso h ≪≫ e = e := by
  simp

end Stacks.CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- **The unit law of the Zariski inverse image of `𝒪`-modules at a pair of identities**: the
composition comparison `(𝟙 W)^* ∘ (𝟙 W)^* ≅ (𝟙 W)^*` at a module is the inverse image along
`𝟙 W` of the identification `(𝟙 W)^* ≅ 𝟭` at that module.

Mathlib states the unit law as
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_left_unitality`, an equation of natural
transformations whose right-hand side is the pseudofunctor's structural transport between
`(f ≫ 𝟙 Y)^*` and `f^*`.  At `f = 𝟙 W` that transport runs between two definitionally equal
functors, so it disappears from the component equation; this is that equation. -/
theorem pullbackComp_id_id_hom_app (W : Scheme.{u}) (𝓖 : W.Modules) :
    (pullbackComp (𝟙 W) (𝟙 W)).hom.app 𝓖 =
      (pullback (𝟙 W)).map ((pullbackId W).hom.app 𝓖) := by
  have h := congr_app (pseudofunctor_left_unitality (𝟙 W)) 𝓖
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.leftUnitor_hom_app,
    eqToHom_app] at h
  have h2 := congrArg (fun k ↦ (pullbackComp (𝟙 W) (𝟙 W)).hom.app 𝓖 ≫ k) h
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] at h2
  exact h2.symm

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- Equal identifications `F ≅ 𝟭 C` give equal whiskered-and-contracted unit laws. -/
private theorem isoWhiskerLeft_trans_rightUnitor_congr {C : Type*} [Category* C] {F : C ⥤ C}
    {e e' : F ≅ 𝟭 C} (h : e = e') :
    Functor.isoWhiskerLeft F e ≪≫ F.rightUnitor = Functor.isoWhiskerLeft F e' ≪≫ F.rightUnitor :=
  congrArg (fun e : F ≅ 𝟭 C ↦ Functor.isoWhiskerLeft F e ≪≫ F.rightUnitor) h

/-- **The unit law of [Stacks Project, Tag 03LU] for the inverse image of `𝒪`-modules at a pair
of identities**: the composition comparison `(𝟙 X)^* ∘ (𝟙 X)^* ≅ (𝟙 X)^*` is the unit law
`AlgebraicGeometry.Space.modulePullbackIdIso` whiskered with the inverse image along `𝟙 X`.

`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left` is this for
the unit datum of a coherence;
`AlgebraicGeometry.Space.modulePushforwardCoherence_modulePullbackIdIso` identifies that datum,
for the coherence this repository constructs, with the identification that carries the 03LU
tag. -/
theorem modulePullbackCompIso_id_id (X : AlgebraicSpaces B S hS) :
    modulePullbackCompIso B S hS (𝟙 X) (𝟙 X) =
      Functor.isoWhiskerLeft (modulePullback B S hS (𝟙 X)) (modulePullbackIdIso B S hS X) ≪≫
        (modulePullback B S hS (𝟙 X)).rightUnitor :=
  ((modulePushforwardCoherence B S hS).modulePullbackCompIso_id_left (𝟙 X)).trans
    (isoWhiskerLeft_trans_rightUnitor_congr
      (modulePushforwardCoherence_modulePullbackIdIso B S hS X))

/-- **The unit law of [Stacks Project, Tag 03LU] for the inverse image at a morphism presented
as an identity.**  For `m : X ⟶ X` and an equality `hid : m = 𝟙 X`, the composition comparison
of `m^* ∘ m^*` with `(m ≫ m)^*` is the transport along `hid`, followed by the unit law
`AlgebraicGeometry.Space.modulePullbackIdIso`, whiskered with `m^*`.

The transport `hcc` of the target is a hypothesis so that a consumer may supply it at whichever
spelling of the composite its own statement fixes; at a morphism of the site for which `m ≫ m`
and `m` are definitionally equal — `AlgebraicGeometry.Space.representedSpaceMap B S hS (𝟙 T)`
is one, by `AlgebraicGeometry.Space.representedSpaceMap_comp` — it is supplied as `rfl` and then
disappears.

Stated between isomorphisms of functors on purpose; the implementation notes of this file record
that the same substitution performed at a component is a kernel deterministic timeout. -/
theorem modulePullbackCompIso_of_eq_id {X : AlgebraicSpaces B S hS} {m : X ⟶ X} (hid : m = 𝟙 X)
    (hcc : modulePullback B S hS (m ≫ m) = modulePullback B S hS m) :
    modulePullbackCompIso B S hS m m ≪≫ eqToIso hcc =
      Functor.isoWhiskerLeft (modulePullback B S hS m)
          (eqToIso (congrArg (modulePullback B S hS) hid) ≪≫ modulePullbackIdIso B S hS X) ≪≫
        (modulePullback B S hS m).rightUnitor := by
  subst hid
  refine (Stacks.CategoryTheory.trans_eqToIso_of_refl _ hcc).trans ?_
  refine (modulePullbackCompIso_id_id B S hS X).trans ?_
  exact isoWhiskerLeft_trans_rightUnitor_congr
    (Stacks.CategoryTheory.eqToIso_of_refl_trans _ (modulePullbackIdIso B S hS X)).symm

end AlgebraicGeometry.Space

end
