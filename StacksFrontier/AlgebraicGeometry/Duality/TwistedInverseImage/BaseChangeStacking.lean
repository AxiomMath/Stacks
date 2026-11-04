module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionAssociativity

/-!
# Derived direct image around a vertical stack of two commutative squares

Let

```
X' --k--> X
|f'       |f
Y' --l--> Y
|g'       |g
Z' --m--> Z
```

be two commutative squares of schemes stacked vertically, so that the outer rectangle is the
commutative square with horizontal edges `k` and `m` and vertical edges `f' ≫ g'` and `f ≫ g`.
`Stacks.Duality.derivedPushforwardSquareIso` attaches to each of the three squares a comparison of
derived direct image around its two sides, and this file proves that the comparison for the
rectangle is the one assembled from the comparisons for the two squares, the direct images along
the two composite vertical morphisms being read through the composition formula of
`Stacks.Duality.derivedPushforwardCompIso`.

This is the geometric input to [Stacks, Tag 0ATQ] (Lemma 48.5.1), which asserts that for a
vertical stack of two cartesian squares of quasi-compact quasi-separated schemes with `f`, `l` and
`g`, `m` Tor-independent, the base change maps of [Stacks, Tag 0AA6] for the two squares compose
to the base change map for the rectangle. The transformation `ξ` of [Stacks, Tag 0A9K] is by
construction the mate of the comparison treated here, so the identity `ξ_rect = ξ_bot ≫ₕ ξ_top`
that the source's proof reduces to is `CategoryTheory.mateEquiv_hcomp` applied to the identity
below; see
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/BaseChangeMate.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/MateTransport.lean`. No `@[stacks]`
attribute is attached here: nothing below mentions a base change map.

## Main results

All in the namespace `Stacks.Duality`.

* `derivedPushforwardCompIso_eqToIso_left` and `derivedPushforwardCompIso_eqToIso_right` — the
  composition formula for derived direct image is compatible with a transport along an equality
  of morphisms in either argument.
* `derivedPushforwardSquareIso_vcomp` — **the vertical stacking identity**, on the unbounded
  derived categories.
* `quasiCoherentDerivedPushforwardSquareIso_vcomp` — the same on the quasi-coherent derived
  categories, componentwise from the ambient one.

## Implementation notes

*The content is the cocycle identity, used three times.* Unfolding
`Stacks.Duality.derivedPushforwardSquareIso` turns both sides into chains built from the
compositor `Stacks.Duality.derivedPushforwardCompIso`, transports along the commutativity of the
squares, and associators. Three instances of
`Stacks.Duality.derivedPushforwardCompIso_cocycle` — for `(k, f, g)`, for `(f', g', m)` and for
`(f', l, g)` — and the two transport compatibilities above identify the two chains; the three
transports compose because an equality of morphisms of schemes is a proposition.

*Why the rearrangement is hoisted into lemmas with variable data.* Every object occurring in the
chains is a composite of derived functors on an unbounded derived category, and the two sides
spell the three-fold composite along the rectangle with different bracketings of the underlying
morphism: `(k ≫ f) ≫ g` on one side and `k ≫ f ≫ g` on the other. Composition of morphisms of
schemes is associative definitionally, but only through the unfolding of a locally ringed space
composition, so deciding such an identification makes the kernel unfold
`Stacks.Duality.derivedPushforward`, and a proof that performs the rearrangement in place exhausts
its budget — `simp` on the assembled goal reports no progress, because the goal is ill-typed at
reducible transparency. `stackingChase` below therefore carries out the whole rearrangement with
every subterm a variable in an arbitrary category, and `isoWhiskerLeft_trans₃`,
`isoWhiskerRight_trans₃` split a whiskered chain in the same way; the unifier reconciles the two
spellings once, at the application site.

## References

* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

/-! ### The rearrangement, with variable data -/

section Chase

/-- The rearrangement underlying `Stacks.Duality.derivedPushforwardSquareIso_vcomp`, with every
object and every isomorphism a variable. The hypotheses are, in order: the splittings of the two
whiskered square comparisons, the three instances of the cocycle identity for the compositor, the
two compatibilities of the compositor with a transport, and the composition of the two
transports. -/
private theorem stackingChase {𝒞 : Type*} [Category 𝒞]
    {A B C₀ D₀ E₀ F₀ G₀ H₀ U U' V V' Y₀ Z₀ T : 𝒞}
    {α : B ≅ A} {β : C₀ ≅ B} {Γ : C₀ ≅ D₀} {γ₁ : C₀ ≅ U} {γ₂ : U ≅ U'} {γ₃ : D₀ ≅ U'}
    {δ : D₀ ≅ E₀} {Ε : E₀ ≅ F₀} {ε₁ : E₀ ≅ Y₀} {ε₂ : Y₀ ≅ Z₀} {ε₃ : F₀ ≅ Z₀}
    {φ : G₀ ≅ F₀} {ψ : G₀ ≅ H₀}
    {cA : A ≅ V} {cU : U ≅ V} {cU' : U' ≅ V'} {cY : Y₀ ≅ V'} {cZ : Z₀ ≅ T} {cH : H₀ ≅ T}
    {ew : V ≅ T} {q₁ : V ≅ V'} {q₂ : V' ≅ T}
    (hΓ : Γ = γ₁ ≪≫ γ₂ ≪≫ γ₃.symm) (hΕ : Ε = ε₁ ≪≫ ε₂ ≪≫ ε₃.symm)
    (h₁ : γ₁ ≪≫ cU = β ≪≫ α ≪≫ cA)
    (h₂ : ψ ≪≫ cH = φ ≪≫ ε₃ ≪≫ cZ)
    (h₃ : γ₃ ≪≫ cU' = δ ≪≫ ε₁ ≪≫ cY)
    (h₄ : cU.symm ≪≫ γ₂ ≪≫ cU' = q₁)
    (h₅ : cY.symm ≪≫ ε₂ ≪≫ cZ = q₂)
    (h₆ : ew = q₁ ≪≫ q₂) :
    cA ≪≫ ew ≪≫ cH.symm =
      α.symm ≪≫ β.symm ≪≫ Γ ≪≫ δ ≪≫ Ε ≪≫ φ.symm ≪≫ ψ := by
  simp only [Iso.ext_iff, Iso.trans_hom, Iso.symm_hom] at h₁ h₂ h₃ h₄ h₅ h₆
  refine Iso.ext ?_
  simp only [hΓ, hΕ, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have eA : cA.hom = α.inv ≫ β.inv ≫ γ₁.hom ≫ cU.hom := by rw [h₁]; simp
  have eU : cU.hom ≫ q₁.hom = γ₂.hom ≫ cU'.hom := by rw [← h₄]; simp
  have eU' : cU'.hom = γ₃.inv ≫ δ.hom ≫ ε₁.hom ≫ cY.hom := by rw [← h₃]; simp
  have eY : cY.hom ≫ q₂.hom = ε₂.hom ≫ cZ.hom := by rw [← h₅]; simp
  have eZ : cZ.hom ≫ cH.inv = ε₃.inv ≫ φ.inv ≫ ψ.hom := by
    rw [(Iso.eq_comp_inv cH).2 h₂]; simp
  rw [h₆, eA]
  slice_lhs 4 5 => rw [eU]
  slice_lhs 5 5 => rw [eU']
  slice_lhs 8 9 => rw [eY]
  slice_lhs 9 10 => rw [eZ]

/-- Whiskering on the left splits a composite of three isomorphisms whose last factor is
inverted. Stated with variable data, so that the application site pays no unfolding. -/
private theorem isoWhiskerLeft_trans₃ {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) {G H K L : D ⥤ E} (a : G ≅ H) (b : H ≅ K) (c : L ≅ K) :
    isoWhiskerLeft F (a ≪≫ b ≪≫ c.symm) =
      isoWhiskerLeft F a ≪≫ isoWhiskerLeft F b ≪≫ (isoWhiskerLeft F c).symm := by
  simp only [isoWhiskerLeft_trans, isoWhiskerLeft_symm]

/-- Whiskering on the right splits a composite of three isomorphisms whose last factor is
inverted. Stated with variable data, so that the application site pays no unfolding. -/
private theorem isoWhiskerRight_trans₃ {C D E : Type*} [Category C] [Category D] [Category E]
    {G H K L : C ⥤ D} (a : G ≅ H) (b : H ≅ K) (c : L ≅ K) (F : D ⥤ E) :
    isoWhiskerRight (a ≪≫ b ≪≫ c.symm) F =
      isoWhiskerRight a F ≪≫ isoWhiskerRight b F ≪≫ (isoWhiskerRight c F).symm := by
  simp only [isoWhiskerRight_trans, isoWhiskerRight_symm]

end Chase

/-! ### The compositor and transports along equalities of morphisms -/

section Transport

/-- **The composition formula for derived direct image is compatible with a transport in its
first argument.** For `p : a = a'` the two identifications of `R(a ≫ b)_*` with `R(a')_* ⋙ Rb_*`
— one through `p` whiskered by `Rb_*`, one through the transport along `p ≫ b` — agree. -/
theorem derivedPushforwardCompIso_eqToIso_left {P Q R : Scheme.{u}} {a a' : P ⟶ Q} (b : Q ⟶ R)
    (p : a = a') :
    (derivedPushforwardCompIso a b).symm ≪≫
        isoWhiskerRight (eqToIso (congrArg (fun t : P ⟶ Q => derivedPushforward t) p))
            (derivedPushforward b) ≪≫
          derivedPushforwardCompIso a' b =
      eqToIso (congrArg (fun t : P ⟶ R => derivedPushforward t) (congrArg (· ≫ b) p)) := by
  subst p
  simp

/-- **The composition formula for derived direct image is compatible with a transport in its
second argument.** The mirror of `Stacks.Duality.derivedPushforwardCompIso_eqToIso_left`. -/
theorem derivedPushforwardCompIso_eqToIso_right {P Q R : Scheme.{u}} (a : P ⟶ Q) {b b' : Q ⟶ R}
    (p : b = b') :
    (derivedPushforwardCompIso a b).symm ≪≫
        isoWhiskerLeft (derivedPushforward a)
            (eqToIso (congrArg (fun t : Q ⟶ R => derivedPushforward t) p)) ≪≫
          derivedPushforwardCompIso a b' =
      eqToIso (congrArg (fun t : P ⟶ R => derivedPushforward t) (congrArg (a ≫ ·) p)) := by
  subst p
  simp

end Transport

/-! ### The vertical stacking identity -/

section Stacking

variable {X' X Y' Y Z' Z : Scheme.{u}} (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
  (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)

/-- **Derived direct image around a vertical stack of two commutative squares of schemes.** For

```
X' --k--> X
|f'       |f
Y' --l--> Y
|g'       |g
Z' --m--> Z
```

the comparison `Stacks.Duality.derivedPushforwardSquareIso` of derived direct image around the two
sides of the outer rectangle is the comparison for the upper square, whiskered by `Rg_*`, followed
by the comparison for the lower square, whiskered by `R(f')_*`, the direct images along the two
composite vertical morphisms being read through the composition formula
`Stacks.Duality.derivedPushforwardCompIso`.

This is the input to [Stacks, Tag 0ATQ] described in the module documentation. -/
theorem derivedPushforwardSquareIso_vcomp (w : k ≫ f ≫ g = (f' ≫ g') ≫ m)
    (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m) :
    derivedPushforwardSquareIso k (f' ≫ g') (f ≫ g) m w =
      isoWhiskerLeft (derivedPushforward k) (derivedPushforwardCompIso f g).symm ≪≫
        (associator (derivedPushforward k) (derivedPushforward f)
            (derivedPushforward g)).symm ≪≫
          isoWhiskerRight (derivedPushforwardSquareIso k f' f l w₁) (derivedPushforward g) ≪≫
            associator (derivedPushforward f') (derivedPushforward l) (derivedPushforward g) ≪≫
              isoWhiskerLeft (derivedPushforward f')
                  (derivedPushforwardSquareIso l g' g m w₂) ≪≫
                (associator (derivedPushforward f') (derivedPushforward g')
                    (derivedPushforward m)).symm ≪≫
                  isoWhiskerRight (derivedPushforwardCompIso f' g')
                    (derivedPushforward m) :=
  stackingChase (isoWhiskerRight_trans₃ _ _ _ (derivedPushforward g))
    (isoWhiskerLeft_trans₃ (derivedPushforward f') _ _ _)
    (derivedPushforwardCompIso_cocycle k f g)
    (derivedPushforwardCompIso_cocycle f' g' m) (derivedPushforwardCompIso_cocycle f' l g)
    (derivedPushforwardCompIso_eqToIso_left g w₁)
    (derivedPushforwardCompIso_eqToIso_right f' w₂) (eqToIso_trans _ _).symm

end Stacking

/-! ### The vertical stacking identity on the quasi-coherent derived categories -/

section QuasiCoherentStacking

variable {X' X Y' Y Z' Z : Scheme.{u}} (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
  (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
  (hpushk : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward k).obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushl : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward l).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z'.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushm : ∀ (K : quasiCoherentDerivedCategory Z') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward m).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  (hpushf'g' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z'.Modules i).obj
      ((derivedPushforward (f' ≫ g')).obj K.obj)).IsQuasicoherent)

/-- **Derived direct image around a vertical stack of two commutative squares, on the
quasi-coherent derived categories.** `Stacks.Duality.derivedPushforwardSquareIso_vcomp` read on
the full subcategories of complexes with quasi-coherent cohomology, for a stack along each of
whose seven morphisms — the five edges, and the two composite verticals — derived direct image
preserves quasi-coherence of cohomology. Every isomorphism involved is the ambient one
componentwise, so the identity is the ambient one at each object. -/
theorem quasiCoherentDerivedPushforwardSquareIso_vcomp (w : k ≫ f ≫ g = (f' ≫ g') ≫ m)
    (w₁ : k ≫ f = f' ≫ l) (w₂ : l ≫ g = g' ≫ m) :
    quasiCoherentDerivedPushforwardSquareIso k (f' ≫ g') (f ≫ g) m hpushk hpushfg hpushf'g'
        hpushm w =
      isoWhiskerLeft (quasiCoherentDerivedPushforward k hpushk)
          (quasiCoherentDerivedPushforwardCompIso f g hpushf hpushg hpushfg).symm ≪≫
        (associator (quasiCoherentDerivedPushforward k hpushk)
            (quasiCoherentDerivedPushforward f hpushf)
            (quasiCoherentDerivedPushforward g hpushg)).symm ≪≫
          isoWhiskerRight (quasiCoherentDerivedPushforwardSquareIso k f' f l hpushk hpushf
              hpushf' hpushl w₁) (quasiCoherentDerivedPushforward g hpushg) ≪≫
            associator (quasiCoherentDerivedPushforward f' hpushf')
                (quasiCoherentDerivedPushforward l hpushl)
                (quasiCoherentDerivedPushforward g hpushg) ≪≫
              isoWhiskerLeft (quasiCoherentDerivedPushforward f' hpushf')
                  (quasiCoherentDerivedPushforwardSquareIso l g' g m hpushl hpushg hpushg'
                    hpushm w₂) ≪≫
                (associator (quasiCoherentDerivedPushforward f' hpushf')
                    (quasiCoherentDerivedPushforward g' hpushg')
                    (quasiCoherentDerivedPushforward m hpushm)).symm ≪≫
                  isoWhiskerRight (quasiCoherentDerivedPushforwardCompIso f' g' hpushf'
                    hpushg' hpushf'g') (quasiCoherentDerivedPushforward m hpushm) := by
  have amb := congrArg Iso.hom (derivedPushforwardSquareIso_vcomp k f' f l g' g m w w₁ w₂)
  refine Iso.ext (NatTrans.ext (funext fun K => ?_))
  apply ObjectProperty.hom_ext
  have h := NatTrans.congr_app amb K.obj
  simp only [quasiCoherentDerivedPushforwardSquareIso, quasiCoherentDerivedPushforwardCompIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, ObjectProperty.isoMk_hom,
    ObjectProperty.isoMk_inv, ObjectProperty.homMk_hom] at h ⊢
  exact h

end QuasiCoherentStacking

end Stacks.Duality

end
