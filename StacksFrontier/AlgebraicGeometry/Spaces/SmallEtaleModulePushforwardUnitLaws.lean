module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# The unit laws of the composition comparisons of Stacks 03LU

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces the direct image `f_*` of
`𝒪`-modules together with the comparison `f_* ∘ g_* ≅ (f ≫ g)_*`.  Pseudofunctoriality of that
assignment asks for an identification `(𝟙 X)_* ≅ 𝟭` and for three coherences: associativity,
which is `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`, and the two unit laws.

This file proves that the two unit laws carry **no information beyond the associativity
coherence**: as soon as the direct image along an identity is isomorphic to the identity functor
by *some* isomorphism, there is a canonical isomorphism — a normalisation of the given one
against the comparison at `(𝟙 X, 𝟙 X)` — for which both unit laws hold.  The structure
`AlgebraicGeometry.Space.ModulePushforwardCoherence` is therefore equivalent to the bare
statement `∀ X, (𝟙 X)_* ≅ 𝟭`, which mentions no comparison and no coherence.

The mechanism is general and is isolated in the `CategoryTheory.Functor` namespace.  Let
`P : 𝒜 ⥤ 𝒜` carry a composition comparison `m : P ⋙ P ≅ P` and let `v : P ≅ 𝟭 𝒜` be arbitrary.
Transporting `m` along `v` turns it into an automorphism of `𝟭 𝒜`, and dividing `v` by that
automorphism gives the unique isomorphism `P ≅ 𝟭 𝒜` carrying `m` to the unitor; this is
`CategoryTheory.Functor.idIsoOfCompIso`.  The associativity coherence, read at a single object,
says exactly that a comparison `P ⋙ F ≅ F` is determined at the objects in the image of `P`,
and naturality then propagates it to all objects, where it becomes the unit law for the
normalised isomorphism.

## Main definitions

* `CategoryTheory.Functor.idIsoOfCompIso`: the normalisation of an isomorphism `P ≅ 𝟭` against a
  composition comparison `P ⋙ P ≅ P`.

## Main results

* `CategoryTheory.Functor.compIso_eq_isoWhiskerRight_idIsoOfCompIso` and
  `CategoryTheory.Functor.compIso_eq_isoWhiskerLeft_idIsoOfCompIso`: the two unit laws for the
  normalised isomorphism, from the associativity cocycle law read at a single object.
* `AlgebraicGeometry.Space.modulePushforwardCompIso_id_comp_app` and
  `AlgebraicGeometry.Space.modulePushforwardCompIso_comp_id_app`: the associativity coherence of
  Stacks 03LU at a triple two of whose members are identities, read at a single module.
* `AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso`: **the pseudofunctoriality data of
  Stacks 03LU from the sole datum `(𝟙 X)_* ≅ 𝟭`**, the associativity coherence and both unit
  laws being supplied.

## Implementation notes

What remains for an unconditional `AlgebraicGeometry.Space.ModulePushforwardCoherence` is
therefore one isomorphism `modulePushforward B S hS (𝟙 X) ≅ 𝟭`, with no compatibility attached.
Its underlying sheaf-of-sets half is cheap: `AlgebraicGeometry.Space.smallEtaleDirectImage` along
an identity is the spaces-étale direct image of `AlgebraicGeometry.Space.spacesBaseChange_id`
conjugated by the comparison equivalence of Stacks 03G1.  What is missing is the scalar half: the
direct image restricts scalars along `AlgebraicGeometry.Space.structureSharp`, so the
isomorphism exists exactly when the structure map of an identity is the identity under that
conjugation, which is the statement that the étale chart `V` itself is initial among the charts
of `X` over `X ×_X V` and that `AlgebraicGeometry.Space.chartBaseChangeMap` at it is an
identity.

Composition in `AlgebraicGeometry.Space.AlgebraicSpaces` is unital and associative by
definitional unfolding, so `𝟙 X ≫ 𝟙 X` and `𝟙 X` are the same morphism, and the associativity
coherence at `(𝟙 X, 𝟙 X, f)` is already a statement about the comparison at `(𝟙 X, f)`; the two
spellings are not syntactically equal, and the rewrites along reflexivity below replace the
longer one by the shorter.  Ascribing the shorter type to the whole cocycle equation instead
sends the elaborator into a reduction of `AlgebraicGeometry.Space.modulePushforward` that does
not terminate, for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompTransport.lean`.

Everything in the general section is stated at the level of isomorphisms of functors, with the
passage to a single object confined to `CategoryTheory.Functor.cocycle_app_of_iso`, for the
reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {C : Type u₂} [Category.{v₂} C]

/-- An isomorphism of an endofunctor with the identity functor is carried by that endofunctor to
its own component: `P.map (v.hom.app M) = v.hom.app (P.obj M)`.

This is naturality of `v` at the component `v.hom.app M`, which is itself an isomorphism. -/
theorem map_app_of_isoToId {P : A ⥤ A} (v : P ≅ 𝟭 A) (M : A) :
    P.map (v.hom.app M) = v.hom.app (P.obj M) := by
  have h := v.hom.naturality (v.hom.app M)
  simp only [Functor.id_map] at h
  exact (cancel_mono (v.hom.app M)).1 h

/-- **The normalisation of an isomorphism `P ≅ 𝟭` against a composition comparison.**  Given
`m : P ⋙ P ≅ P` and an arbitrary isomorphism `v : P ≅ 𝟭`, this is the isomorphism `P ≅ 𝟭`
obtained by dividing `v` by the automorphism of `𝟭` that `v` turns `m` into; it is the unique
one carrying `m` to the unitor. -/
def idIsoOfCompIso {P : A ⥤ A} (m : P ⋙ P ≅ P) (v : P ≅ 𝟭 A) : P ≅ 𝟭 A :=
  (leftUnitor P).symm ≪≫ (isoWhiskerRight v P).symm ≪≫ m ≪≫ v

/-- The components of `CategoryTheory.Functor.idIsoOfCompIso`. -/
theorem idIsoOfCompIso_hom_app {P : A ⥤ A} (m : P ⋙ P ≅ P) (v : P ≅ 𝟭 A) (M : A) :
    (idIsoOfCompIso m v).hom.app M =
      P.map (v.inv.app M) ≫ m.hom.app M ≫ v.hom.app M := by
  simp [idIsoOfCompIso]

/-- **The first unit law for the normalised isomorphism.**  A comparison `c : P ⋙ F ≅ F` whose
components at the objects in the image of `P` are the images under `F` of the components of
`m : P ⋙ P ≅ P` is the comparison whiskered from
`CategoryTheory.Functor.idIsoOfCompIso`.

The hypothesis is the associativity cocycle law for `m` and `c`, read at a single object. -/
theorem compIso_eq_isoWhiskerRight_idIsoOfCompIso {P : A ⥤ A} {F : A ⥤ C} (m : P ⋙ P ≅ P)
    (c : P ⋙ F ≅ F) (v : P ≅ 𝟭 A)
    (hc : ∀ M, c.hom.app (P.obj M) = F.map (m.hom.app M)) :
    c = isoWhiskerRight (idIsoOfCompIso m v) F ≪≫ leftUnitor F := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  have hnat := c.hom.naturality (v.hom.app M)
  simp only [Functor.comp_map, hc M] at hnat
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.leftUnitor_hom_app, idIsoOfCompIso_hom_app, F.map_comp]
  rw [← hnat, ← Category.assoc, ← F.map_comp, ← P.map_comp]
  simp

/-- **The second unit law for the normalised isomorphism.**  A comparison `d : F ⋙ Q ≅ F` such
that `Q` carries its components to the components of `m : Q ⋙ Q ≅ Q` is the comparison whiskered
from `CategoryTheory.Functor.idIsoOfCompIso`.

The hypothesis is the associativity cocycle law for `d` and `m`, read at a single object. -/
theorem compIso_eq_isoWhiskerLeft_idIsoOfCompIso {Q : C ⥤ C} {F : A ⥤ C} (m : Q ⋙ Q ≅ Q)
    (d : F ⋙ Q ≅ F) (v : Q ≅ 𝟭 C)
    (hd : ∀ M, m.hom.app (F.obj M) = Q.map (d.hom.app M)) :
    d = isoWhiskerLeft F (idIsoOfCompIso m v) ≪≫ rightUnitor F := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  have hnat := v.hom.naturality (d.hom.app M)
  simp only [Functor.id_map, Functor.comp_obj] at hnat
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, idIsoOfCompIso_hom_app, hd M]
  rw [hnat, ← map_app_of_isoToId v (F.obj M), ← Category.assoc, ← Q.map_comp]
  simp

/-- If the last two legs of the cocycle law for `P` and `Q` are the same comparison `c`, then `r`
carries the component of `P` to the component of `Q`. -/
private theorem map_app_eq_of_cocycle {B₀ B₁ B₂ : Type*} [Category B₀] [Category B₁] [Category B₂]
    {p : B₀ ⥤ B₁} {q : B₁ ⥤ B₁} {r : B₁ ⥤ B₂} {pqr : B₀ ⥤ B₂} (P : p ⋙ q ≅ p) (Q : q ⋙ r ≅ r)
    {c c' : p ⋙ r ≅ pqr} (h : isoWhiskerLeft p Q ≪≫ c = (associator p q r).symm ≪≫
      isoWhiskerRight P r ≪≫ c') (hc : c' = c) (N : B₀) :
    r.map (P.hom.app N) = Q.hom.app (p.obj N) := by
  subst hc
  have key := Functor.cocycle_app_of_iso P Q c' c' h N
  exact (cancel_mono _).1 (by simpa only [Iso.app_hom] using key)

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 03LU, the associativity coherence at `(𝟙 X, 𝟙 X, f)`.**  The comparison
`(𝟙 X)_* ∘ f_* ≅ f_*` at a direct image along `𝟙 X` is the image under `f_*` of the comparison
`(𝟙 X)_* ∘ (𝟙 X)_* ≅ (𝟙 X)_*`. -/
theorem modulePushforwardCompIso_id_comp_app (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardCompIso B S hS (𝟙 X) f).hom.app
        ((modulePushforward B S hS (𝟙 X)).obj M) =
      (modulePushforward B S hS f).map
        ((modulePushforwardCompIso B S hS (𝟙 X) (𝟙 X)).hom.app M) := by
  exact (map_app_eq_of_cocycle (modulePushforwardCompIso B S hS (𝟙 X) (𝟙 X))
    (modulePushforwardCompIso B S hS (𝟙 X) f)
    (modulePushforwardCompIso_assoc B S hS (𝟙 X) (𝟙 X) f) rfl M).symm

/-- **Stacks 03LU, the associativity coherence at `(f, 𝟙 Y, 𝟙 Y)`.**  The comparison
`(𝟙 Y)_* ∘ (𝟙 Y)_* ≅ (𝟙 Y)_*` at a direct image along `f` is the image under `(𝟙 Y)_*` of the
comparison `f_* ∘ (𝟙 Y)_* ≅ f_*`. -/
theorem modulePushforwardCompIso_comp_id_app (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforwardCompIso B S hS (𝟙 Y) (𝟙 Y)).hom.app
        ((modulePushforward B S hS f).obj M) =
      (modulePushforward B S hS (𝟙 Y)).map
        ((modulePushforwardCompIso B S hS f (𝟙 Y)).hom.app M) := by
  exact (map_app_eq_of_cocycle (modulePushforwardCompIso B S hS f (𝟙 Y))
    (modulePushforwardCompIso B S hS (𝟙 Y) (𝟙 Y))
    (modulePushforwardCompIso_assoc B S hS f (𝟙 Y) (𝟙 Y)) rfl M).symm

/-- **Pseudofunctoriality of the direct image of `𝒪`-modules of Stacks 03LU from the sole datum
`(𝟙 X)_* ≅ 𝟭`.**

The associativity coherence is `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`, and both
unit laws hold for the normalisation
`CategoryTheory.Functor.idIsoOfCompIso` of the given isomorphism against the comparison at
`(𝟙 X, 𝟙 X)`.  No compatibility is asked of the input. -/
def modulePushforwardCoherenceOfIdIso
    (v : ∀ X : AlgebraicSpaces B S hS,
      modulePushforward B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2)) :
    ModulePushforwardCoherence B S hS where
  idIso X :=
    Functor.idIsoOfCompIso (modulePushforwardCompIso B S hS (𝟙 X) (𝟙 X)) (v X)
  assoc f g h := modulePushforwardCompIso_assoc B S hS f g h
  id_comp {X _Y} f :=
    Functor.compIso_eq_isoWhiskerRight_idIsoOfCompIso
      (modulePushforwardCompIso B S hS (𝟙 X) (𝟙 X))
      (modulePushforwardCompIso B S hS (𝟙 X) f) (v X)
      (modulePushforwardCompIso_id_comp_app B S hS f)
  comp_id {_X Y} f :=
    Functor.compIso_eq_isoWhiskerLeft_idIsoOfCompIso
      (modulePushforwardCompIso B S hS (𝟙 Y) (𝟙 Y))
      (modulePushforwardCompIso B S hS f (𝟙 Y)) (v Y)
      (modulePushforwardCompIso_comp_id_app B S hS f)

end AlgebraicGeometry.Space

end
