module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.PullbackGenericFibrePushout
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.GenericFibreCartesianOfGood

/-!
# The generic fibre of a base change, and the pushout of residue fields it presents

Let `p : X ⟶ Y` be a relatively representable morphism of decent algebraic spaces and `x` a
point of `X` such that

```
Spec κ(x) ⟶ X
    ↓         ↓ p
Spec κ(p x) ⟶ Y
```

is cartesian. For a morphism `b : V ⟶ Y` from a representable space and a point `w` of `V` over
`p x`, the fibre of `X ×_Y V ⟶ V` over `Spec κ(w)` is the base change of `Spec κ(x)` along
`Spec κ(w) ⟶ Spec κ(p x)`. Taking global sections, the ring of that fibre is a pushout of
`κ(w)` and `κ(x)` over `κ(p x)`, in the sense of `Algebra.IsPushout`.

## Main results

* `AlgebraicGeometry.Space.exists_yoneda_map_comp_residueFieldMorphism`: the residue-field square
  of a morphism of decent algebraic spaces at a point `x` and a point `y` with `f x = y`, the
  morphism of residue-field spectra being `Spec` of a homomorphism of residue fields.
* `AlgebraicGeometry.Space.exists_isPullback_baseChange_of_isPullback`: in any category, the fibre
  of a base change is the base change of the fibre.
* `AlgebraicGeometry.Space.algebraIsPushout_appTop_of_isPullback_yoneda`: a cartesian square of
  the big fppf site over `S`, three of whose corners have affine underlying scheme, has global
  sections a pushout of algebras.
* `AlgebraicGeometry.Space.exists_isPullback_toScheme_fibre_baseChange`: the fibre of
  `X ×_Y V ⟶ V` over the field-valued point of `w` is the base change of `Spec κ(x)` along
  `Spec κ(w) ⟶ Spec κ(p x)`.

## References

* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EMW](https://stacks.math.columbia.edu/tag/0EMW)
* [Stacks Project, Tag 0END](https://stacks.math.columbia.edu/tag/0END)
* [Stacks Project, Tag 0EQ4](https://stacks.math.columbia.edu/tag/0EQ4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### The residue-field square at a named image point -/

section ResidueSquare

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The residue-field square of a morphism of decent algebraic spaces, at a named image point.
For `f : X ⟶ Y` a morphism of decent algebraic spaces, `x` a point of `X` and `y` a point of `Y`
with `f x = y`, there are a homomorphism of residue fields `φ : κ(y) → κ(x)` and a morphism
`g : Spec κ(x) ⟶ Spec κ(y)` of the site, with underlying morphism of schemes `Spec φ`, making

```
Spec κ(x) ⟶ X
    ↓         ↓ f
Spec κ(y) ⟶ Y
```

commute, the horizontal morphisms being the monomorphic representatives of Stacks 0EMW. -/
theorem exists_yoneda_map_comp_residueFieldMorphism (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) {y : points B S hS Y}
    (hy : pointsMap B S hS X f x = y) :
    ∃ (φ : residueField B S hS Y hdecY y →+* residueField B S hS X hdecX x)
      (g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
        (residueFieldRepresentative B S hS Y hdecY y).1.siteObject B S hS Y),
      B.inclusion.map g.left = Spec.map (CommRingCat.ofHom φ) ∧
        residueFieldMorphism B S hS X hdecX x ≫ f =
          yoneda.map g ≫ residueFieldMorphism B S hS Y hdecY y := by
  subst hy
  obtain ⟨g, hgSpec, hg⟩ := residueFieldHom_spec B S hS X Y hY hdecX hdecY f x
  exact ⟨_, g, hgSpec, hg.symm⟩

end ResidueSquare

/-! ### The pasting -/

section Paste

variable {C : Type*} [Category C] {X Y W SX SY SW U G : C}

/-- The fibre of a base change is the base change of the fibre. Let `p : X ⟶ Y` and
`b : W ⟶ Y` be morphisms, let

```
SX ⟶ X          U ⟶ X           G ⟶ U
↓      ↓ p      ↓     ↓ p       ↓     ↓
SY ⟶ Y          W ⟶ Y           SW ⟶ W
```

be cartesian — so `SX` is the fibre of `p` over `SY ⟶ Y`, `U` is `W ×_Y X`, and `G` is the fibre
of `U ⟶ W` over `SW ⟶ W` — and let `SW ⟶ W ⟶ Y` factor as `SW ⟶ SY ⟶ Y`. Then

```
G  ⟶ SX
↓      ↓
SW ⟶ SY
```

is cartesian, with the top morphism the one induced by the universal property of the first
square. -/
theorem exists_isPullback_baseChange_of_isPullback {p : X ⟶ Y} {b : W ⟶ Y} {ιX : SX ⟶ X}
    {ιY : SY ⟶ Y} {ιW : SW ⟶ W} {gp : SX ⟶ SY} {gb : SW ⟶ SY} {fst : U ⟶ W} {snd : U ⟶ X}
    {gfst : G ⟶ SW} {gsnd : G ⟶ U} (hfib : IsPullback ιX gp p ιY)
    (hbc : IsPullback snd fst p b) (hgf : IsPullback gsnd gfst fst ιW)
    (hcomm : ιW ≫ b = gb ≫ ιY) :
    ∃ a : G ⟶ SX, a ≫ ιX = gsnd ≫ snd ∧ a ≫ gp = gfst ≫ gb ∧ IsPullback a gfst gp gb := by
  have hbig : IsPullback (gsnd ≫ snd) gfst p (gb ≫ ιY) := by
    rw [← hcomm]
    exact hgf.paste_horiz hbc
  exact ⟨_, hfib.lift_fst _ _ _, hfib.lift_snd _ _ _, hbig.of_right' hfib⟩

end Paste

/-! ### Global sections of a cartesian square of the site -/

section Pushout

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

/-- A cartesian square of the big fppf site over `S` with three affine corners has global
sections a pushout of algebras. For a square of the site whose image under `yoneda` is
cartesian, and whose corners `Q`, `R` and `W` have affine underlying scheme, the ring
`Γ(P, 𝒪_P)` is the base change of `Γ(Q, 𝒪_Q)` along `Γ(W, 𝒪_W) → Γ(R, 𝒪_R)`. -/
theorem algebraIsPushout_appTop_of_isPullback_yoneda {P Q R W : BigFppfOver B S hS} {a : P ⟶ Q}
    {c : P ⟶ R} {d : Q ⟶ W} {e : R ⟶ W}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj R)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W)]
    (h : IsPullback (yoneda.map a) (yoneda.map c) (yoneda.map d) (yoneda.map e)) :
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map d).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj R, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map e).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map a).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map c).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map a ≫
        (BigFppfOver.toScheme B S hS).map d).appTop.hom.toAlgebra
    haveI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) :=
      .of_algebraMap_eq'
        (show ((BigFppfOver.toScheme B S hS).map a ≫
              (BigFppfOver.toScheme B S hS).map d).appTop.hom =
            ((BigFppfOver.toScheme B S hS).map a).appTop.hom.comp
              ((BigFppfOver.toScheme B S hS).map d).appTop.hom by
          rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp])
    haveI : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) :=
      .of_algebraMap_eq'
        (show ((BigFppfOver.toScheme B S hS).map a ≫
              (BigFppfOver.toScheme B S hS).map d).appTop.hom =
            ((BigFppfOver.toScheme B S hS).map c).appTop.hom.comp
              ((BigFppfOver.toScheme B S hS).map e).appTop.hom by
          have hw : a ≫ d = c ≫ e :=
            yoneda.map_injective (by rw [Functor.map_comp, Functor.map_comp]; exact h.w)
          rw [← Functor.map_comp, hw, Functor.map_comp, Scheme.Hom.comp_appTop,
            CommRingCat.hom_comp])
    Algebra.IsPushout Γ((BigFppfOver.toScheme B S hS).obj W, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj Q, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj R, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj P, ⊤) :=
  algebraIsPushout_appTop_of_isPullback
    ((IsPullback.of_map_of_faithful yoneda h).map (BigFppfOver.toScheme B S hS))

end Pushout

/-! ### The fibre of a base change of a relatively representable morphism -/

section Fibre

attribute [local instance] AlgebraicGeometry.hasPullbacks_bigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : X ⟶ Y}

/-- The fibre of a base change is the base change of the fibre, for algebraic spaces. Let
`p : X ⟶ Y` be a relatively representable morphism of decent algebraic spaces, let `x` be a
point of `X`, and suppose the fibre of `p` over the chosen field-valued point of `p x` is the
chosen field-valued point of `x`, that is that

```
Spec κ(x)  ⟶ X
    ↓          ↓ p
Spec κ(p x) ⟶ Y
```

is cartesian, the morphism `Spec κ(x) ⟶ Spec κ(p x)` of the site being `g`. Let `b : V ⟶ Y` be a
morphism from a representable space and let `w` be a point of `V` with `b w = p x`. Then there is
an object `G` of the site, and morphisms making

```
G ⟶ X ×_Y V          G  ⟶ Spec κ(x)
↓        ↓            ↓        ↓ g
Spec κ(w) ⟶ V        Spec κ(w) ⟶ Spec κ(p x)
```

both cartesian, the morphism `e : Spec κ(w) ⟶ Spec κ(p x)` of the site having underlying
morphism of schemes `Spec φ` for a homomorphism of residue fields `φ : κ(p x) → κ(w)`. -/
theorem exists_isPullback_toScheme_fibre_baseChange
    (hrep : yoneda.relativelyRepresentable p) (hY : IsAlgebraicSpace B S hS Y)
    (hdecX : IsDecentSpace B S hS X) (hdecY : IsDecentSpace B S hS Y) (x : points B S hS X)
    {g : (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X ⟶
      (residueFieldRepresentative B S hS Y hdecY
        (pointsMap B S hS X p x)).1.siteObject B S hS Y}
    (hfib : IsPullback (residueFieldMorphism B S hS X hdecX x) (yoneda.map g) p
      (residueFieldMorphism B S hS Y hdecY (pointsMap B S hS X p x)))
    (V : BigFppfOver B S hS) (b : yoneda.obj V ⟶ Y) (w : points B S hS (yoneda.obj V))
    (hw : pointsMap B S hS (yoneda.obj V) b w = pointsMap B S hS X p x) :
    ∃ (G : BigFppfOver B S hS)
      (iV : (residueFieldRepresentative B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V)
          w).1.siteObject B S hS (yoneda.obj V) ⟶ V)
      (u : G ⟶ hrep.pullback b)
      (q : G ⟶ (residueFieldRepresentative B S hS (yoneda.obj V)
          (isDecentSpace_yoneda B S hS V) w).1.siteObject B S hS (yoneda.obj V))
      (r : G ⟶ (residueFieldRepresentative B S hS X hdecX x).1.siteObject B S hS X)
      (e : (residueFieldRepresentative B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V)
          w).1.siteObject B S hS (yoneda.obj V) ⟶
        (residueFieldRepresentative B S hS Y hdecY
          (pointsMap B S hS X p x)).1.siteObject B S hS Y)
      (φ : residueField B S hS Y hdecY (pointsMap B S hS X p x) →+*
        residueField B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V) w),
      yoneda.map iV = residueFieldMorphism B S hS (yoneda.obj V)
          (isDecentSpace_yoneda B S hS V) w ∧
        B.inclusion.map e.left = Spec.map (CommRingCat.ofHom φ) ∧
        IsPullback (yoneda.map u) (yoneda.map q) (yoneda.map (hrep.snd b)) (yoneda.map iV) ∧
        IsPullback (yoneda.map r) (yoneda.map q) (yoneda.map g) (yoneda.map e) := by
  obtain ⟨φ, e, hφ, he⟩ := exists_yoneda_map_comp_residueFieldMorphism B S hS hY
    (isDecentSpace_yoneda B S hS V) hdecY b w hw
  set iV : (residueFieldRepresentative B S hS (yoneda.obj V) (isDecentSpace_yoneda B S hS V)
      w).1.siteObject B S hS (yoneda.obj V) ⟶ V :=
    yoneda.preimage (residueFieldMorphism B S hS (yoneda.obj V)
      (isDecentSpace_yoneda B S hS V) w)
  have hiV : yoneda.map iV = residueFieldMorphism B S hS (yoneda.obj V)
      (isDecentSpace_yoneda B S hS V) w := yoneda.map_preimage _
  have hgf : IsPullback (yoneda.map (Limits.pullback.fst (hrep.snd b) iV))
      (yoneda.map (Limits.pullback.snd (hrep.snd b) iV)) (yoneda.map (hrep.snd b))
      (yoneda.map iV) := (IsPullback.of_hasPullback (hrep.snd b) iV).map yoneda
  obtain ⟨a, -, -, ha⟩ := exists_isPullback_baseChange_of_isPullback hfib (hrep.isPullback b)
    hgf (by rw [hiV, he])
  refine ⟨Limits.pullback (hrep.snd b) iV, iV, Limits.pullback.fst (hrep.snd b) iV,
    Limits.pullback.snd (hrep.snd b) iV, yoneda.preimage a, e, φ, hiV, hφ, hgf, ?_⟩
  rwa [yoneda.map_preimage]

end Fibre

end AlgebraicGeometry.Space

end
