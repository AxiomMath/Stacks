module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BaseChangeCondition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.BasePasting
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkOfDerivedPushforward

/-!
# Pasting of the base change map for abelian sheaves on small étale sites

Let

```
X₂ --v₂--> X₁ --v₁--> X₀
|g₂         |g₁        |g₀
v           v          v
S₂ --u₂--> S₁ --u₁--> S₀
```

be two commutative squares of schemes sharing the edge `g₁`, so that `g₁ ≫ u₁ = v₁ ≫ g₀` and
`g₂ ≫ u₂ = v₂ ≫ g₁`. The outer rectangle commutes as well, and this file proves that the base
change map of the outer rectangle is the composite of the base change maps of the two squares,
read through the composition comparisons for the inverse images along the two composite
horizontal legs `u₂ ≫ u₁` and `v₂ ≫ v₁`:

`ψ₀ = (u₂ ≫ u₁)^{-1}-to-u₂^{-1}u₁^{-1} ∘ u₂^{-1}ψ₁ ∘ ψ₂ ∘ g₂_*(v₂^{-1}v₁^{-1}-to-(v₂ ≫ v₁)^{-1})`

where `ψ_i` is `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` of the square `i`.

Everything here is *underived*: the maps compared are the underived base change maps
`g_*(-)^{-1} ⟶ (-)^{-1}g_*`, which are mates of the identifications of the two composite direct
images around a square. The pasting law is therefore the pasting law for mates, and the only
mathematical input is the associativity pentagon of the comparison of direct images along a
composite, `Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc`, applied to the three
threefold composites `(v₂, v₁, g₀)`, `(v₂, g₁, u₁)` and `(g₂, u₂, u₁)` through the rectangle.

## Main definitions

* `Stacks.EtaleCohomology.smallEtalePushforwardAbComp'` —
  `Stacks.EtaleCohomology.smallEtalePushforwardComp'` for abelian coefficients, with the
  composite named rather than written out, so that no transport along `Category.assoc` enters
  any statement.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso` — the identification
  `e_* g_* ≅ h_* (f')_*` of the two composite direct images around a commutative square, in the
  form that exhibits it as a composite of two `smallEtalePushforwardAbComp'`s and nothing else.

## Main results

* `Stacks.EtaleCohomology.mateEquiv_smallEtaleBaseChangeAb` — the mate of the base change map is
  the square comparison of direct images.
* `Stacks.EtaleCohomology.conjugateEquiv_symm_hom_eq_leftAdjointUniq` — the canonical comparison
  of two left adjoints of isomorphic right adjoints is the transpose of the comparison of the
  right adjoints under conjugation.
* `Stacks.EtaleCohomology.conjugateEquiv_smallEtalePullbackAbCompIso_hom` and
  `..._inv` — the instance of that for
  `Stacks.EtaleCohomology.smallEtalePullbackAbCompIso`.
* `Stacks.EtaleCohomology.smallEtaleSquarePushforwardIso_paste_app` — the pasting of the square
  comparisons of direct images, the geometric content.
* `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste` and
  `Stacks.EtaleCohomology.smallEtaleBaseChangeAb_paste_app` — **the pasting law**, as an identity
  of 2-squares and evaluated at a sheaf.

## Implementation notes

*No tag is placed.* Stacks 0E47 states the pasting law for the *derived* base change map; the
underived identity proved here is one step of its proof, not the source's statement, so no
`@[stacks 0E47]` attribute appears. What the derived statement additionally needs is recorded
below.

*The two vocabularies for the comparison of direct images.*
`Stacks.EtaleCohomology.smallEtalePushforwardAbCompIso`, through which
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is defined, writes the composite out and glues
the commutativity of the square in by `eqToIso`;
`Stacks.EtaleCohomology.smallEtalePushforwardComp'`, which carries the associativity pentagon,
takes the composite as a named morphism together with an equation. The two are related by
`Stacks.EtaleCohomology.smallEtalePushforwardAbComp'_eq`, and the pasting argument runs entirely
in the second vocabulary: in the first, the pentagon would have to be transported along
`Category.assoc` at every use.

*Why the algebra is on variables.* `Stacks.EtaleCohomology.paste_algebra` is the cancellation
that turns the three pentagons into the pasting identity, stated for fourteen morphisms in an
abstract category. The morphisms it is applied to are components of comparisons of composite
direct images, and at those types the rearrangement is unreadable.

*What the derived pasting still needs.* `Stacks.EtaleCohomology.higherBaseChangeMapAb` is the
degree-`q` cohomology of `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`, which is the
descent of the underived mate along the derived-functor unit of `Rg_*`
(`Stacks.Cohomology.BaseChange.derived`, characterized by
`Stacks.Cohomology.BaseChange.derived_fac`). Two further steps separate the identity proved here
from the pasting law for the higher direct images:

1. the descent of this identity along `Stacks.Cohomology.BaseChange.derived`. By
   `CategoryTheory.Functor.rightDerived_ext` it suffices to compare the two sides after the
   derived-functor unit of `Rg_*`, where `Stacks.Cohomology.BaseChange.derived_fac` replaces each
   factor by `Stacks.Cohomology.BaseChange.onHomotopy`; the identity then needs the comparison
   `R(G) ⋙ R(G') ≅ R(G₀)` for exact `G`, `G'` with `G ⋙ G' ≅ G₀`, its compatibility with the
   degreewise comparisons `Stacks.Cohomology.BaseChange.exactUnit_isIso` supplies, and the
   behaviour of `Stacks.Cohomology.BaseChange.mapPlus` under
   `CategoryTheory.Functor.mapHomotopyCategoryPlusCompIso`. None of the three is carried.
2. the transport of the result through `Stacks.EtaleCohomology.baseChangeSourceIso` and
   `Stacks.EtaleCohomology.baseChangeTargetIso`, which needs the compatibility of
   `Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso` with a composite of exact functors.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The comparison of direct images along a composite, with the composite named -/

/-- The direct image along a composite is the composite of the direct images, for abelian
coefficients and with the composite named: `Stacks.EtaleCohomology.smallEtalePushforwardComp'` at
`Ab`, in the vocabulary of `Stacks.EtaleCohomology.smallEtalePushforwardAb`. The body is
`smallEtalePushforwardComp'` itself, so nothing is reproved. -/
def smallEtalePushforwardAbComp' {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    smallEtalePushforwardAb f ⋙ smallEtalePushforwardAb g ≅ smallEtalePushforwardAb fg :=
  smallEtalePushforwardComp' f g fg hfg Ab.{u + 1}

/-- **The associativity pentagon of the comparison of direct images**, for abelian coefficients:
`Stacks.EtaleCohomology.smallEtalePushforwardComp'_assoc` at `Ab`. -/
theorem smallEtalePushforwardAbComp'_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    Functor.isoWhiskerRight (smallEtalePushforwardAbComp' f g fg hfg)
          (smallEtalePushforwardAb h) ≪≫
        smallEtalePushforwardAbComp' fg h fgh h₁ =
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (smallEtalePushforwardAb f)
            (smallEtalePushforwardAbComp' g h gh hgh) ≪≫
          smallEtalePushforwardAbComp' f gh fgh h₂ :=
  smallEtalePushforwardComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂ Ab.{u + 1}

/-- The associativity pentagon, evaluated at a sheaf. This is the form the pasting argument
consumes: the associators of the pentagon are identities on components. -/
theorem smallEtalePushforwardAbComp'_assoc_app {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh)
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (smallEtalePushforwardAb h).map
          ((smallEtalePushforwardAbComp' f g fg hfg).hom.app F) ≫
        (smallEtalePushforwardAbComp' fg h fgh h₁).hom.app F =
      (smallEtalePushforwardAbComp' g h gh hgh).hom.app
          ((smallEtalePushforwardAb f).obj F) ≫
        (smallEtalePushforwardAbComp' f gh fgh h₂).hom.app F := by
  simpa using congrArg (fun z : _ ≅ _ => NatTrans.app z.hom F)
    (smallEtalePushforwardAbComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂)

/-- **The two vocabularies for the comparison of direct images agree.** The named-composite form
is the written-out form followed by the transport along the naming equation. -/
theorem smallEtalePushforwardAbComp'_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    smallEtalePushforwardAbComp' f g fg hfg =
      smallEtalePushforwardAbCompIso f g ≪≫
        eqToIso (congrArg smallEtalePushforwardAb hfg.symm) := by
  subst hfg
  have hbc : smallEtaleBaseChangeComp' f g (f ≫ g) rfl = smallEtaleBaseChangeComp f g := by
    simp [smallEtaleBaseChangeComp']
  simp only [smallEtalePushforwardAbComp', smallEtalePushforwardComp', hbc,
    smallEtalePushforwardAbCompIso, eqToIso_refl]
  exact (Iso.trans_refl _).symm

/-- At a literal composite the two vocabularies coincide on the nose. -/
theorem smallEtalePushforwardAbComp'_rfl {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtalePushforwardAbComp' f g (f ≫ g) rfl = smallEtalePushforwardAbCompIso f g := by
  rw [smallEtalePushforwardAbComp'_eq]
  simp

/-! ### The square comparison of direct images, and the mate -/

section Square

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- The identification `e_* g_* ≅ h_* (f')_*` of the two composite direct images around the
commutative square `h ≫ f' = e ≫ g`, written as a composite of two comparisons with the common
diagonal `h ≫ f'` named. This is the comparison the base change map
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` is the mate of. -/
def smallEtaleSquarePushforwardIso :
    smallEtalePushforwardAb e ⋙ smallEtalePushforwardAb g ≅
      smallEtalePushforwardAb h ⋙ smallEtalePushforwardAb f' :=
  smallEtalePushforwardAbComp' e g (h ≫ f') w ≪≫
    (smallEtalePushforwardAbComp' h f' (h ≫ f') rfl).symm

/-- The square comparison, in the written-out vocabulary that
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb` uses. -/
theorem smallEtaleSquarePushforwardIso_eq :
    smallEtaleSquarePushforwardIso f' g h e w =
      (smallEtalePushforwardAbCompIso e g).trans
        ((eqToIso (congrArg smallEtalePushforwardAb w.symm)).trans
          (smallEtalePushforwardAbCompIso h f').symm) := by
  rw [smallEtaleSquarePushforwardIso, smallEtalePushforwardAbComp'_eq e g (h ≫ f') w,
    smallEtalePushforwardAbComp'_rfl]
  simp [Iso.trans_assoc]

/-- The base change map is the mate of the square comparison, in the named-composite
vocabulary. -/
theorem smallEtaleBaseChangeAb_eq_mate :
    smallEtaleBaseChangeAb f' g h e w =
      Stacks.Cohomology.BaseChange.mate (smallEtaleAdjunctionAb f') (smallEtaleAdjunctionAb e)
        (smallEtalePushforwardAb g) (smallEtalePushforwardAb h)
        (smallEtaleSquarePushforwardIso f' g h e w) := by
  rw [smallEtaleSquarePushforwardIso_eq]
  rfl

/-- **The mate of the base change map is the square comparison of direct images.** This is the
bridge that makes Mathlib's pasting lemmas for `CategoryTheory.mateEquiv` applicable: the
identity to be proved for the base change maps becomes an identity between comparisons of
composite direct images. -/
theorem mateEquiv_smallEtaleBaseChangeAb :
    mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')
        (TwoSquare.mk _ _ _ _ (smallEtaleBaseChangeAb f' g h e w)) =
      TwoSquare.mk _ _ _ _ (smallEtaleSquarePushforwardIso f' g h e w).hom := by
  rw [smallEtaleBaseChangeAb_eq_mate, Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm]
  exact (mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')).apply_symm_apply _

end Square

/-! ### The comparison of inverse images along a composite, transposed -/

/-- **The canonical comparison of two left adjoints of isomorphic right adjoints is the transpose
of the comparison of the right adjoints.** For `adjA : L₁ ⊣ R`, `adjB : L₂ ⊣ R'` and
`ε : R' ≅ R`, the comparison `L₁ ≅ L₂` produced by
`CategoryTheory.Adjunction.leftAdjointUniq` from the transported adjunction is
`CategoryTheory.conjugateEquiv`-transpose of `ε.hom`. Both sides are determined by their
transpose under `adjA`, and there the identity is the formula for the unit of a right-transported
adjunction. -/
theorem conjugateEquiv_symm_hom_eq_leftAdjointUniq {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R R' : D ⥤ C} (adjA : L₁ ⊣ R) (adjB : L₂ ⊣ R') (ε : R' ≅ R) :
    (conjugateEquiv adjB adjA).symm ε.hom =
      (Adjunction.leftAdjointUniq adjA (adjB.ofNatIsoRight ε)).hom := by
  refine NatTrans.ext (funext fun c => (adjA.homEquiv c (L₂.obj c)).injective ?_)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.unit_leftAdjointUniq_hom_app, ← unit_conjugateEquiv_symm]
  simp [Adjunction.ofNatIsoRight]

section PullbackComp

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)

/-- **The comparison of inverse images along a composite is the transpose of the comparison of
direct images.** -/
theorem conjugateEquiv_smallEtalePullbackAbCompIso_hom :
    conjugateEquiv (smallEtaleAdjunctionAb (a ≫ b))
        ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
        (smallEtalePullbackAbCompIso a b).hom =
      (smallEtalePushforwardAbCompIso a b).inv := by
  have h : (smallEtalePullbackAbCompIso a b).hom =
      (conjugateEquiv (smallEtaleAdjunctionAb (a ≫ b))
        ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))).symm
        (smallEtalePushforwardAbCompIso a b).symm.hom :=
    (conjugateEquiv_symm_hom_eq_leftAdjointUniq
      ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
      (smallEtaleAdjunctionAb (a ≫ b)) (smallEtalePushforwardAbCompIso a b).symm).symm
  rw [h]
  exact (conjugateEquiv (smallEtaleAdjunctionAb (a ≫ b))
    ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))).apply_symm_apply _

/-- The same identity for the inverse of the comparison: conjugation takes an isomorphism to an
isomorphism, so the two directions determine each other. -/
theorem conjugateEquiv_smallEtalePullbackAbCompIso_inv :
    conjugateEquiv ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
        (smallEtaleAdjunctionAb (a ≫ b)) (smallEtalePullbackAbCompIso a b).inv =
      (smallEtalePushforwardAbCompIso a b).hom := by
  have h : conjugateIsoEquiv (smallEtaleAdjunctionAb (a ≫ b))
        ((smallEtaleAdjunctionAb b).comp (smallEtaleAdjunctionAb a))
        (smallEtalePullbackAbCompIso a b) =
      (smallEtalePushforwardAbCompIso a b).symm :=
    Iso.ext (conjugateEquiv_smallEtalePullbackAbCompIso_hom a b)
  exact congrArg Iso.inv h

end PullbackComp

/-! ### The pasting law -/

section Paste

variable {X₀ X₁ X₂ S₀ S₁ S₂ : Scheme.{u}} (g₀ : X₀ ⟶ S₀) (g₁ : X₁ ⟶ S₁) (g₂ : X₂ ⟶ S₂)
  (u₁ : S₁ ⟶ S₀) (u₂ : S₂ ⟶ S₁) (v₁ : X₁ ⟶ X₀) (v₂ : X₂ ⟶ X₁)
  (w₁ : g₁ ≫ u₁ = v₁ ≫ g₀) (w₂ : g₂ ≫ u₂ = v₂ ≫ g₁)

include w₁ w₂ in
/-- **The outer rectangle of two horizontally composable commutative squares commutes.** -/
theorem smallEtaleRectangle_comm : g₂ ≫ u₂ ≫ u₁ = (v₂ ≫ v₁) ≫ g₀ := by
  rw [reassoc_of% w₂, w₁, Category.assoc]

/-- The cancellation that turns three instances of the associativity pentagon into the pasting
identity for the square comparisons.

Stated on variables in a single category: the morphisms it is applied to are components of
comparisons of composite direct images, and at those types the rearrangement is unreadable. The
three pentagons enter as `hP₁`, `hP₂`, `hP₃`; the four remaining hypotheses are that the four
comparisons being inverted are invertible. -/
private theorem paste_algebra {E : Type*} [Category* E] {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ : E}
    {a : O₁ ⟶ O₂} {a' : O₂ ⟶ O₁} {b : O₂ ⟶ O₃} {d : O₄ ⟶ O₃} {d' : O₃ ⟶ O₄}
    {ee : O₁ ⟶ O₅} {gg : O₆ ⟶ O₅} {gg' : O₅ ⟶ O₆} {l : O₅ ⟶ O₃} {m : O₇ ⟶ O₃}
    {hh : O₆ ⟶ O₇} {jj : O₈ ⟶ O₇} {jj' : O₇ ⟶ O₈} {kk : O₈ ⟶ O₄}
    (ha : a' ≫ a = 𝟙 O₂) (hd : d ≫ d' = 𝟙 O₄) (hg : gg' ≫ gg = 𝟙 O₅)
    (hj : jj' ≫ jj = 𝟙 O₇)
    (hP₁ : a ≫ b = ee ≫ l) (hP₂ : hh ≫ m = gg ≫ l) (hP₃ : jj ≫ m = kk ≫ d) :
    b ≫ d' = a' ≫ ee ≫ gg' ≫ hh ≫ jj' ≫ kk := by
  have hl : gg' ≫ hh ≫ m = l := by rw [hP₂, ← Category.assoc, hg, Category.id_comp]
  have hm : jj' ≫ kk = m ≫ d' := by
    have h1 : jj' ≫ jj ≫ m ≫ d' = m ≫ d' := by
      rw [← Category.assoc jj' jj, hj, Category.id_comp]
    rw [← h1, ← Category.assoc jj m d', hP₃, Category.assoc, hd, Category.comp_id]
  rw [hm, reassoc_of% hl, ← reassoc_of% hP₁, reassoc_of% ha]

/-- **The pasting of the square comparisons of direct images**, which is the geometric content of
the pasting law. The comparison of the two composite direct images around the outer rectangle is
the composite of the comparisons of the two squares, read through the comparisons of the direct
images along the two composite horizontal legs. -/
theorem smallEtaleSquarePushforwardIso_paste_app
    (𝓖 : Sheaf (smallEtaleTopology X₂) Ab.{u + 1}) :
    (smallEtaleSquarePushforwardIso (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).hom.app 𝓖 =
      (smallEtalePushforwardAb g₀).map
          ((smallEtalePushforwardAbComp' v₂ v₁ (v₂ ≫ v₁) rfl).inv.app 𝓖) ≫
        (smallEtaleSquarePushforwardIso u₁ g₀ g₁ v₁ w₁).hom.app
            ((smallEtalePushforwardAb v₂).obj 𝓖) ≫
          (smallEtalePushforwardAb u₁).map
              ((smallEtaleSquarePushforwardIso u₂ g₁ g₂ v₂ w₂).hom.app 𝓖) ≫
            (smallEtalePushforwardAbComp' u₂ u₁ (u₂ ≫ u₁) rfl).hom.app
              ((smallEtalePushforwardAb g₂).obj 𝓖) := by
  have hL : g₂ ≫ u₂ ≫ u₁ = v₂ ≫ g₁ ≫ u₁ := by rw [reassoc_of% w₂]
  have hM : g₂ ≫ u₂ ≫ u₁ = (g₂ ≫ u₂) ≫ u₁ := (Category.assoc _ _ _).symm
  have hP₁ := smallEtalePushforwardAbComp'_assoc_app v₂ v₁ g₀ (v₂ ≫ v₁) rfl (g₁ ≫ u₁) w₁
    (g₂ ≫ u₂ ≫ u₁) (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) hL 𝓖
  have hP₂ := smallEtalePushforwardAbComp'_assoc_app v₂ g₁ u₁ (g₂ ≫ u₂) w₂ (g₁ ≫ u₁) rfl
    (g₂ ≫ u₂ ≫ u₁) hM hL 𝓖
  have hP₃ := smallEtalePushforwardAbComp'_assoc_app g₂ u₂ u₁ (g₂ ≫ u₂) rfl (u₂ ≫ u₁) rfl
    (g₂ ≫ u₂ ≫ u₁) hM rfl 𝓖
  simp only [smallEtaleSquarePushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  exact paste_algebra (by simp) (by simp) (by simp) (by simp) hP₁ hP₂ hP₃

include w₁ w₂ in
/-- **The pasting law for the underived base change map of abelian small étale sheaves.** For two
horizontally composable commutative squares of schemes, the base change map of the outer
rectangle is the composite of the base change maps of the two squares, read through the
comparisons of the inverse images along the two composite horizontal legs.

The hypotheses are the commutativity of the two squares and nothing else: the squares need not be
cartesian, and no finiteness, separatedness or torsion condition enters, inverse image of abelian
sheaves being exact for every morphism of schemes. -/
theorem smallEtaleBaseChangeAb_paste :
    TwoSquare.mk _ _ _ _
        (smallEtaleBaseChangeAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)) =
      ((TwoSquare.vComp (TwoSquare.mk _ _ _ _ (smallEtaleBaseChangeAb u₁ g₀ g₁ v₁ w₁))
            (TwoSquare.mk _ _ _ _ (smallEtaleBaseChangeAb u₂ g₁ g₂ v₂ w₂))).whiskerLeft
          (smallEtalePullbackAbCompIso v₂ v₁).hom).whiskerRight
        (smallEtalePullbackAbCompIso u₂ u₁).inv := by
  apply (mateEquiv (smallEtaleAdjunctionAb (v₂ ≫ v₁))
    (smallEtaleAdjunctionAb (u₂ ≫ u₁))).injective
  rw [mateEquiv_conjugateEquiv_vcomp (smallEtaleAdjunctionAb (v₂ ≫ v₁))
      ((smallEtaleAdjunctionAb u₁).comp (smallEtaleAdjunctionAb u₂))
      (smallEtaleAdjunctionAb (u₂ ≫ u₁)),
    conjugateEquiv_mateEquiv_vcomp (smallEtaleAdjunctionAb (v₂ ≫ v₁))
      ((smallEtaleAdjunctionAb v₁).comp (smallEtaleAdjunctionAb v₂))
      ((smallEtaleAdjunctionAb u₁).comp (smallEtaleAdjunctionAb u₂)),
    mateEquiv_hcomp (smallEtaleAdjunctionAb v₁) (smallEtaleAdjunctionAb u₁)
      (smallEtaleAdjunctionAb v₂) (smallEtaleAdjunctionAb u₂),
    conjugateEquiv_smallEtalePullbackAbCompIso_hom,
    conjugateEquiv_smallEtalePullbackAbCompIso_inv,
    mateEquiv_smallEtaleBaseChangeAb, mateEquiv_smallEtaleBaseChangeAb,
    mateEquiv_smallEtaleBaseChangeAb, ← smallEtalePushforwardAbComp'_rfl v₂ v₁,
    ← smallEtalePushforwardAbComp'_rfl u₂ u₁]
  refine TwoSquare.ext _ _ fun 𝓖 => ?_
  simpa using smallEtaleSquarePushforwardIso_paste_app g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂ 𝓖

include w₁ w₂ in
/-- **The pasting law, evaluated at a sheaf.** -/
theorem smallEtaleBaseChangeAb_paste_app (F : Sheaf (smallEtaleTopology X₀) Ab.{u + 1}) :
    (smallEtaleBaseChangeAb (u₂ ≫ u₁) g₀ g₂ (v₂ ≫ v₁)
          (smallEtaleRectangle_comm g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂)).app F =
      (smallEtalePullbackAbCompIso u₂ u₁).inv.app ((smallEtalePushforwardAb g₀).obj F) ≫
        (smallEtalePullbackAb u₂).map ((smallEtaleBaseChangeAb u₁ g₀ g₁ v₁ w₁).app F) ≫
          (smallEtaleBaseChangeAb u₂ g₁ g₂ v₂ w₂).app ((smallEtalePullbackAb v₁).obj F) ≫
            (smallEtalePushforwardAb g₂).map
              ((smallEtalePullbackAbCompIso v₂ v₁).hom.app F) := by
  simpa using congr_app (smallEtaleBaseChangeAb_paste g₀ g₁ g₂ u₁ u₂ v₁ v₂ w₁ w₂) F

end Paste

end Stacks.EtaleCohomology

end
