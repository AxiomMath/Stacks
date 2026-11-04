module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackAssoc
public import StacksFrontier.CategoryTheory.Adjunction.UniqueComp

/-!
# Pseudofunctoriality of the direct image of modules, and what it gives the inverse image

Stacks 03LU attaches to a morphism `f : X ⟶ Y` of algebraic spaces the adjoint pair
`(f^*, f_*)` on `𝒪`-modules together with the comparisons
`f_* ∘ g_* ≅ (f ≫ g)_*` and `g^* ∘ f^* ≅ (f ≫ g)^*`, the second being the mate of the first.
Saying that the assignment `f ↦ (f^*, f_*)` is pseudofunctorial is saying that these
comparisons satisfy the associativity coherence and the two unit laws.

This file records those coherences **for the direct images** as a single piece of data,
`AlgebraicGeometry.Space.ModulePushforwardCoherence`, and derives from it every corresponding
statement about the inverse images, with no further input.  The derivation is mechanical: the
comparison of inverse images is the comparison of left adjoints induced by the comparison of
right adjoints — `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_comp` — and Mathlib
proves that such an induced comparison inherits the coherences of the comparison it is induced
by.

The structure is **inhabited with no hypothesis**, by
`AlgebraicGeometry.Space.modulePushforwardCoherence`; see the implementation notes below for the
four fields and where each is proved.  A result below stated with an explicit
`ModulePushforwardCoherence` hypothesis is therefore unconditional in substance.

Isolating the direct-image side is the whole point.  The direct images are the ones given by an
explicit construction: `AlgebraicGeometry.Space.modulePushforward` is the direct image of
sheaves of sets with its scalars restricted, and its comparison
`AlgebraicGeometry.Space.modulePushforwardCompIso` is the geometric comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp` of Stacks 03G2, part (3), on underlying
sheaves of sets.  The inverse images are characterized only by a universal property, so a
coherence for them has no direct proof at all; it is the transpose of the one for direct
images.

## Main definitions

* `AlgebraicGeometry.Space.ModulePushforwardCoherence`: the identity law `(𝟙 X)_* ≅ 𝟭` for the
  direct image together with the associativity coherence and the two unit laws of
  `AlgebraicGeometry.Space.modulePushforwardCompIso`.
* `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackIdIso`: **the unit law
  `(𝟙 X)^* ≅ 𝟭`** for the inverse image.
* `AlgebraicGeometry.Space.modulePullbackTriangle`: the comparison of the inverse image along a
  morphism that *equals* a composite with the iterated inverse image, and
  `AlgebraicGeometry.Space.modulePullbackSquare`, the comparison of the two iterated inverse
  images along the two sides of a commuting square.
* `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackEquivalence` and
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackHomEquiv`: the inverse
  image along an isomorphism of algebraic spaces is an equivalence, hence fully faithful.

## Main results

* `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_assoc`: **the
  associativity coherence of `g^* ∘ f^* ≅ (f ≫ g)^*`**, and
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIsoAssoc`, the same in
  the form of the predicate
  `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`, so that the reindexing calculus built
  on that predicate becomes available.
* `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left` and
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_right`: the two
  unit laws of the comparison of inverse images.
* `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_comp` and
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_id`: the same two
  coherences for composites presented as single morphisms, which is the form a consumer
  indexed by a category of test objects needs, with
  `AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackTriangle_comp'` the first
  of them solved for the comparison along the triple composite.

## Implementation notes

Composition in `AlgebraicGeometry.Space.AlgebraicSpaces` is associative and unital by
definitional unfolding — a morphism of algebraic spaces is a morphism of presheaves of types,
where composition is composition of functions — so `(f ≫ g) ≫ h` and `f ≫ g ≫ h` are the same
morphism to the elaborator, as are `𝟙 X ≫ f` and `f`.  No transport along `Category.assoc`,
`Category.id_comp` or `Category.comp_id` appears below, and the coherences are stated with the
two bracketings written out and nothing in between.

**`AlgebraicGeometry.Space.modulePullbackTriangle` is an isomorphism of FUNCTORS, and every
statement about it is made at that level.**  This is not a matter of taste.  The comparison
transports along an equality of morphisms of algebraic spaces, so it contains
`eqToIso (congrArg (AlgebraicGeometry.Space.modulePullback B S hS ·) h)`, and the kernel does
not finish checking a *proof* of any statement that mentions the underlying morphism of such an
isomorphism: a module-indexed version of the comparison whose own definition projected,
`(modulePullbackTriangle B S hS hk M).hom = eqToHom _ ≫ _`, is a deterministic timeout proved by
`rfl`, by `simp`, by `Iso.trans_hom`, and in the version defined as a plain morphism rather than
an isomorphism, while the corresponding isomorphism-level statement is immediate and the
morphism-level *tautology* is accepted.  `simp` and `rw` are no help at the morphism level
either: the two sides of the transport are definitionally but not syntactically equal, so a
rewrite motive mentioning them is not syntactically type-correct, and neither `eqToHom_refl` nor
`Category.id_comp` fires.  This is the obstruction recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`, met from the other
side.  Keeping the comparison at the level of functors avoids it entirely and has a second
benefit: its naturality in the module is then a field of the natural transformation rather than
a statement needing proof.

The comparison of direct images is *not* an equality of functors even for a composite of the
morphisms of ringed topoi of Stacks 03G8, for the reason recorded in the implementation notes
of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackComp.lean`: the morphism of
ringed topoi of a composite is only 2-isomorphic to the composite of the morphisms of ringed
topoi.  So the coherences are genuine assertions about
`AlgebraicGeometry.Space.smallToposMorphismTypeU_comp`, the geometric comparison of Stacks 03G2,
part (3), and not unfoldings.

**They are nonetheless theorems, and the structure is inhabited with no hypothesis.**  The
geometric coherence is `AlgebraicGeometry.Space.smallToposMorphismTypeU_comp_assoc`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardAssoc.lean`), carried up to
modules as `AlgebraicGeometry.Space.modulePushforwardCompIso_assoc`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardCompIsoAssoc.lean`); the
identity datum is `AlgebraicGeometry.Space.modulePushforwardIdIso`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackId.lean`), and
`AlgebraicGeometry.Space.modulePushforwardCoherenceOfIdIso` normalises it so that both unit laws
hold.  The assembled term is `AlgebraicGeometry.Space.modulePushforwardCoherence`
(`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePushforwardIdIso.lean`).  The hypothesis
`hc` carried by the results below is therefore dischargeable at every use site, and the
unconditional forms of the two main results live in that file's companion
`SmallEtaleModulePushforwardCompIsoAssoc.lean`
(`AlgebraicGeometry.Space.modulePullbackCompIso_assoc` and
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`).  It is kept as a hypothesis here only
because this file declares the structure and so precedes its construction.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {V W X Y Z : AlgebraicSpaces B S hS}

/-- The comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of inverse images of Stacks 03LU is the comparison
of left adjoints induced by the comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of direct images.

This holds with no hypothesis; it is the normalization that carries every coherence of the
comparison of direct images over to the comparison of inverse images. -/
theorem modulePullbackCompIso_eq_leftAdjointCompIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y Z : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackCompIso B S hS f g =
      Adjunction.leftAdjointCompIso (modulePullbackAdjunction B S hS g)
        (modulePullbackAdjunction B S hS f) (modulePullbackAdjunction B S hS (f ≫ g))
        (modulePushforwardCompIso B S hS f g) :=
  Adjunction.leftAdjointUniq_ofNatIsoRight_comp _ _ _ _

/-- **Pseudofunctoriality of the direct image of `𝒪`-modules of Stacks 03LU.**

The data of an identification `(𝟙 X)_* ≅ 𝟭` of the direct image along an identity with the
identity functor, such that the comparison `f_* ∘ g_* ≅ (f ≫ g)_*` of Stacks 03LU satisfies the
associativity coherence for three composable morphisms and the two unit laws. -/
structure ModulePushforwardCoherence (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) where
  /-- The direct image along an identity is the identity functor. -/
  idIso : ∀ X : AlgebraicSpaces B S hS,
    modulePushforward B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2)
  /-- The associativity coherence: for three composable morphisms the two ways of comparing
  `f_* ∘ g_* ∘ h_*` with `(f ≫ g ≫ h)_*` agree. -/
  assoc : ∀ {W X Y Z : AlgebraicSpaces B S hS} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),
    isoWhiskerLeft (modulePushforward B S hS f) (modulePushforwardCompIso B S hS g h) ≪≫
        modulePushforwardCompIso B S hS f (g ≫ h) =
      (associator (modulePushforward B S hS f) (modulePushforward B S hS g)
          (modulePushforward B S hS h)).symm ≪≫
        isoWhiskerRight (modulePushforwardCompIso B S hS f g)
          (modulePushforward B S hS h) ≪≫
        modulePushforwardCompIso B S hS (f ≫ g) h
  /-- The unit law at the source: the comparison for `𝟙 X ≫ f` is the identity law. -/
  id_comp : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    modulePushforwardCompIso B S hS (𝟙 X) f =
      isoWhiskerRight (idIso X) (modulePushforward B S hS f) ≪≫
        leftUnitor (modulePushforward B S hS f)
  /-- The unit law at the target: the comparison for `f ≫ 𝟙 Y` is the identity law. -/
  comp_id : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    modulePushforwardCompIso B S hS f (𝟙 Y) =
      isoWhiskerLeft (modulePushforward B S hS f) (idIso Y) ≪≫
        rightUnitor (modulePushforward B S hS f)

namespace ModulePushforwardCoherence

/-- **The associativity coherence of the comparison `g^* ∘ f^* ≅ (f ≫ g)^*` of inverse images
of Stacks 03LU.**  For three composable morphisms `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` the two
ways of comparing `h^* ∘ g^* ∘ f^*` with `(f ≫ g ≫ h)^*` agree.

This is the transpose of the associativity coherence of the comparison of direct images. -/
theorem modulePullbackCompIso_assoc (hc : ModulePushforwardCoherence B S hS)
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerLeft (modulePullback B S hS h) (modulePullbackCompIso B S hS f g) ≪≫
        modulePullbackCompIso B S hS (f ≫ g) h =
      (associator (modulePullback B S hS h) (modulePullback B S hS g)
          (modulePullback B S hS f)).symm ≪≫
        isoWhiskerRight (modulePullbackCompIso B S hS g h) (modulePullback B S hS f) ≪≫
        modulePullbackCompIso B S hS f (g ≫ h) := by
  simp only [modulePullbackCompIso_eq_leftAdjointCompIso]
  exact
    Adjunction.leftAdjointCompIso_assoc (modulePullbackAdjunction B S hS h)
      (modulePullbackAdjunction B S hS g) (modulePullbackAdjunction B S hS f)
      (modulePullbackAdjunction B S hS (g ≫ h)) (modulePullbackAdjunction B S hS (f ≫ g))
      (modulePullbackAdjunction B S hS (f ≫ g ≫ h))
      (modulePushforwardCompIso B S hS g h) (modulePushforwardCompIso B S hS f g)
      (modulePushforwardCompIso B S hS (f ≫ g) h)
      (modulePushforwardCompIso B S hS f (g ≫ h)) (hc.assoc f g h)

/-- The associativity coherence of the comparison of inverse images, in the form of the
predicate `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`, which the reindexing calculus
of `StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` consumes. -/
theorem modulePullbackCompIsoAssoc (hc : ModulePushforwardCoherence B S hS) :
    ModulePullbackCompIsoAssoc B S hS where
  hom_app f g h M := by
    have h₂ := NatTrans.congr_app
      (congrArg Iso.hom (hc.modulePullbackCompIso_assoc f g h)) M
    simpa using h₂.symm

variable (hc : ModulePushforwardCoherence B S hS)

/-- **The unit law `(𝟙 X)^* ≅ 𝟭` for the inverse image of `𝒪`-modules of Stacks 03LU**: the
inverse image along an identity is the identity functor.

It is the identity law of the direct image read through uniqueness of a left adjoint. -/
def modulePullbackIdIso (X : AlgebraicSpaces B S hS) :
    modulePullback B S hS (𝟙 X) ≅ 𝟭 (Modules.{u, u} B S hS X.1 X.2) :=
  Adjunction.leftAdjointIdIso (modulePullbackAdjunction B S hS (𝟙 X)) (hc.idIso X)

/-- The comparison of inverse images for `𝟙 X ≫ f` is the unit law `(𝟙 X)^* ≅ 𝟭`. -/
theorem modulePullbackCompIso_id_left (f : X ⟶ Y) :
    modulePullbackCompIso B S hS (𝟙 X) f =
      isoWhiskerLeft (modulePullback B S hS f) (hc.modulePullbackIdIso X) ≪≫
        rightUnitor (modulePullback B S hS f) := by
  rw [modulePullbackCompIso_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_comp_id (modulePullbackAdjunction B S hS f)
    (modulePullbackAdjunction B S hS (𝟙 X)) (modulePushforwardCompIso B S hS (𝟙 X) f)
    (hc.idIso X) (hc.id_comp f)

/-- The comparison of inverse images for `f ≫ 𝟙 Y` is the unit law `(𝟙 Y)^* ≅ 𝟭`. -/
theorem modulePullbackCompIso_id_right (f : X ⟶ Y) :
    modulePullbackCompIso B S hS f (𝟙 Y) =
      isoWhiskerRight (hc.modulePullbackIdIso Y) (modulePullback B S hS f) ≪≫
        leftUnitor (modulePullback B S hS f) := by
  rw [modulePullbackCompIso_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_id_comp (modulePullbackAdjunction B S hS (𝟙 Y))
    (modulePullbackAdjunction B S hS f) (modulePushforwardCompIso B S hS f (𝟙 Y))
    (hc.idIso Y) (hc.comp_id f)

end ModulePushforwardCoherence


/-- The inverse image along a composite `f ≫ g`, presented as the inverse image along a single
morphism `k` with `f ≫ g = k`, compared with the composite of the inverse images.

Taking the composite as a hypothesis rather than writing `f ≫ g` is what lets a consumer
indexed by a category of test objects use the comparison at a morphism that *equals* a
composite without first rewriting; the comparison of Stacks 03LU is the case `k = f ≫ g`,
recorded in `AlgebraicGeometry.Space.modulePullbackTriangle_rfl`. -/
def modulePullbackTriangle (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) :
    modulePullback B S hS k ≅ modulePullback B S hS g ⋙ modulePullback B S hS f :=
  eqToIso (congrArg (modulePullback B S hS) hk.symm) ≪≫
    (modulePullbackCompIso B S hS f g).symm

/-- `AlgebraicGeometry.Space.modulePullbackTriangle` written out. -/
theorem modulePullbackTriangle_eq {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (hk : f ≫ g = k) :
    modulePullbackTriangle B S hS hk =
      eqToIso (congrArg (modulePullback B S hS) hk.symm) ≪≫
        (modulePullbackCompIso B S hS f g).symm := rfl

/-- At the composite itself, the comparison of
`AlgebraicGeometry.Space.modulePullbackTriangle` is the comparison of Stacks 03LU. -/
theorem modulePullbackTriangle_rfl (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePullbackTriangle B S hS (f := f) (g := g) rfl =
      (modulePullbackCompIso B S hS f g).symm := by
  rw [modulePullbackTriangle_eq]
  simp

/-- The comparison depends on the morphism and not on the presentation of it as a composite. -/
theorem modulePullbackTriangle_congr {f : X ⟶ Y} {g : Y ⟶ Z} {k k' : X ⟶ Z}
    (hk : f ≫ g = k) (hk' : f ≫ g = k') (hkk : k = k') :
    modulePullbackTriangle B S hS hk =
      eqToIso (congrArg (modulePullback B S hS) hkk) ≪≫ modulePullbackTriangle B S hS hk' := by
  rw [modulePullbackTriangle_eq, modulePullbackTriangle_eq, ← Iso.trans_assoc, eqToIso_trans]

/-- Replacing the first factor of the composite by an equal morphism changes the comparison
only by the induced identification of the two inverse images. -/
theorem modulePullbackTriangle_congr_left {f f' : X ⟶ Y} (hff : f = f') {g : Y ⟶ Z}
    {k : X ⟶ Z} (hk : f ≫ g = k) (hk' : f' ≫ g = k) :
    modulePullbackTriangle B S hS hk =
      modulePullbackTriangle B S hS hk' ≪≫
        isoWhiskerLeft (modulePullback B S hS g)
          (eqToIso (congrArg (modulePullback B S hS) hff.symm)) := by
  subst hff
  have hE : modulePullbackTriangle B S hS hk = modulePullbackTriangle B S hS hk' := rfl
  rw [hE]
  simp

/-- The comparison of the two iterated inverse images along the two sides of a commuting
square `e ≫ l = r ≫ q` of morphisms of algebraic spaces. -/
def modulePullbackSquare (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V W X Z : AlgebraicSpaces B S hS} {e : V ⟶ W} {l : W ⟶ Z} {r : V ⟶ X} {q : X ⟶ Z}
    {k : V ⟶ Z} (hk : e ≫ l = k) (hk' : r ≫ q = k) :
    modulePullback B S hS l ⋙ modulePullback B S hS e ≅
      modulePullback B S hS q ⋙ modulePullback B S hS r :=
  (modulePullbackTriangle B S hS hk).symm ≪≫ modulePullbackTriangle B S hS hk'

namespace ModulePushforwardCoherence

/-- **The inverse image along an isomorphism of algebraic spaces is an equivalence** of the
categories of `𝒪`-modules, with the inverse image along the inverse isomorphism as its
inverse.

This is the unit law of Stacks 03LU together with the comparison for the two composites
`e ≫ e⁻¹` and `e⁻¹ ≫ e`. -/
def modulePullbackEquivalence (hc : ModulePushforwardCoherence B S hS) (e : X ≅ Y) :
    Modules.{u, u} B S hS Y.1 Y.2 ≌ Modules.{u, u} B S hS X.1 X.2 :=
  CategoryTheory.Equivalence.mk (modulePullback B S hS e.hom) (modulePullback B S hS e.inv)
    ((hc.modulePullbackIdIso Y).symm ≪≫ modulePullbackTriangle B S hS e.inv_hom_id)
    ((modulePullbackTriangle B S hS e.hom_inv_id).symm ≪≫ hc.modulePullbackIdIso X)

/-- The inverse image along an isomorphism of algebraic spaces is fully faithful, so it
identifies the two Hom sets. -/
def modulePullbackHomEquiv (hc : ModulePushforwardCoherence B S hS) (e : X ≅ Y)
    (M N : Modules.{u, u} B S hS Y.1 Y.2) :
    (M ⟶ N) ≃
      ((modulePullback B S hS e.hom).obj M ⟶ (modulePullback B S hS e.hom).obj N) :=
  (hc.modulePullbackEquivalence e).fullyFaithfulFunctor.homEquiv

/-- **The comparison of inverse images along composites is compatible with composition.**  For
`f : V ⟶ W`, `g : W ⟶ X` and `p : X ⟶ Z`, breaking the inverse image along the triple composite
into three steps through `f ≫ g` or through `g ≫ p` gives the same comparison.

This is the associativity coherence of Stacks 03LU, stated for composites presented as single
morphisms, which is the form a consumer indexed by a category of test objects needs. -/
theorem modulePullbackTriangle_comp (hc : ModulePushforwardCoherence B S hS)
    {f : V ⟶ W} {g : W ⟶ X} {p : X ⟶ Z} {k : V ⟶ X} {q : W ⟶ Z} {r : V ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) :
    modulePullbackTriangle B S hS hkr ≪≫
        isoWhiskerLeft (modulePullback B S hS p) (modulePullbackTriangle B S hS hk) =
      modulePullbackTriangle B S hS hr ≪≫
        isoWhiskerRight (modulePullbackTriangle B S hS hq) (modulePullback B S hS f) ≪≫
        Functor.associator (modulePullback B S hS p) (modulePullback B S hS g)
          (modulePullback B S hS f) := by
  subst hk
  subst hq
  rw [modulePullbackTriangle_eq hkr, modulePullbackTriangle_eq hr, modulePullbackTriangle_rfl,
    modulePullbackTriangle_rfl, Iso.trans_assoc, Iso.trans_assoc]
  refine congrArg (fun t ↦ eqToIso (congrArg (modulePullback B S hS) hkr.symm) ≪≫ t) ?_
  have key := hc.modulePullbackCompIso_assoc f g p
  rw [← Iso.symm_eq_iff] at key
  simpa [Functor.isoWhiskerLeft_symm, Functor.isoWhiskerRight_symm] using key

/-- The associativity coherence, solved for the comparison along the triple composite.  This
is the shape `CategoryTheory.Functor.conjHom_comp` consumes. -/
theorem modulePullbackTriangle_comp' (hc : ModulePushforwardCoherence B S hS)
    {f : V ⟶ W} {g : W ⟶ X} {p : X ⟶ Z} {k : V ⟶ X} {q : W ⟶ Z} {r : V ⟶ Z}
    (hk : f ≫ g = k) (hq : g ≫ p = q) (hr : f ≫ q = r) (hkr : k ≫ p = r) :
    modulePullbackTriangle B S hS hkr =
      (modulePullbackTriangle B S hS hr ≪≫
          isoWhiskerRight (modulePullbackTriangle B S hS hq) (modulePullback B S hS f) ≪≫
          Functor.associator (modulePullback B S hS p) (modulePullback B S hS g)
            (modulePullback B S hS f)) ≪≫
        (isoWhiskerLeft (modulePullback B S hS p) (modulePullbackTriangle B S hS hk)).symm := by
  rw [← hc.modulePullbackTriangle_comp hk hq hr hkr, Iso.trans_assoc, Iso.self_symm_id,
    Iso.trans_refl]

/-- **The comparison of inverse images along a composite whose first factor is an identity is
the unit law `(𝟙 X)^* ≅ 𝟭`.** -/
theorem modulePullbackTriangle_id (hc : ModulePushforwardCoherence B S hS)
    {g : X ⟶ Z} (hk : 𝟙 X ≫ g = g) :
    modulePullbackTriangle B S hS hk =
      (Functor.rightUnitor (modulePullback B S hS g)).symm ≪≫
        isoWhiskerLeft (modulePullback B S hS g) (hc.modulePullbackIdIso X).symm := by
  rw [show modulePullbackTriangle B S hS hk = _ from modulePullbackTriangle_rfl (𝟙 X) g,
    hc.modulePullbackCompIso_id_left g]
  simp [Functor.isoWhiskerLeft_symm]

end ModulePushforwardCoherence

end AlgebraicGeometry.Space

end
