module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.VanishingCyclesFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections

/-!
# Sections over the strict henselization base change of a cartesian square

Let `f : X ⟶ S` be a morphism of schemes, let `x̄` be a geometric point of `X`, and consider a
cartesian square with `h : Y ⟶ X`, `e : Y ⟶ T` and `g : T ⟶ S`. The base change of `h` to
`Spec(O^sh_{X,x̄})` maps canonically to the base change of `g` to `Spec(O^sh_{S,f(x̄)})`, and
this morphism is itself the base change of `Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` along the
latter. Consequently, when the morphism of strict henselizations is flat with geometrically
connected fibres, sections of a sheaf of sets over `Spec(O^sh_{S,f(x̄)}) ×_S T` are the sections
of its inverse image over `Spec(O^sh_{X,x̄}) ×_X Y`.

## Main definitions

* `Stacks.EtaleCohomology.strictHenselizationPullback` — the base change of a morphism to the
  strict henselization of its target at a geometric point.
* `Stacks.EtaleCohomology.strictHenselizationPullbackMap` — the canonical morphism
  `Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T` of a cartesian square.

## Main results

* `Stacks.EtaleCohomology.isPullback_strictHenselizationPullbackMap` — that morphism is a base
  change of the morphism of strict henselizations.
* `Stacks.EtaleCohomology.globalSectionsIso_strictHenselizationPullback` — the resulting
  identification of global sections, naturally in the sheaf.

## Implementation notes

The strict henselization of a scheme at a geometric point is taken relative to a big étale
site containing the scheme, which is how it is available here.

Global sections downstairs agreeing with global sections of the inverse image upstairs is Tag
0A3H, whose hypotheses are flatness, quasi-compactness and geometric connectedness of the
fibres. Quasi-compactness is automatic, since a base change of a morphism of affine schemes;
geometric connectedness of the morphism of strict henselizations is the hypothesis of Tag
0F00; flatness of it is an input Tag 0F00 leaves implicit and is carried here as the declared
hypothesis `hflat`.

## References

* [Stacks Project, Tag 0F00](https://stacks.math.columbia.edu/tag/0F00)
* [Stacks Project, Tag 0A3H](https://stacks.math.columbia.edu/tag/0A3H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe w w' u v

namespace Stacks.EtaleCohomology

section Pasting

variable {C : Type w} [Category.{w'} C]

/-- In a cartesian square `Y = X ×_S T`, the morphism `P ×_X Y ⟶ Q ×_S T` determined by a
commutative square `m ≫ q = p ≫ f` is a base change of `m`: both fibre products are
`P ×_S T`. -/
private theorem isPullback_baseChange_of_isPullback {P Q X Y S T QY QT : C}
    {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T} (sq : IsPullback h e f g)
    {p : P ⟶ X} {q : Q ⟶ S} {m : P ⟶ Q} (hm : m ≫ q = p ≫ f)
    {aY : QY ⟶ P} {bY : QY ⟶ Y} (sqY : IsPullback aY bY p h)
    {aT : QT ⟶ Q} {bT : QT ⟶ T} (sqT : IsPullback aT bT q g)
    {n : QY ⟶ QT} (hn₁ : n ≫ aT = aY ≫ m) (hn₂ : n ≫ bT = bY ≫ e) :
    IsPullback aY n m aT :=
  IsPullback.of_bot (by rw [hn₂, hm]; exact sqY.paste_vert sq) hn₁.symm sqT

end Pasting

section StrictHenselizationPullback

variable (B : BigEtaleSite.{u})

/-- The base change `Spec(O^sh_{Z,z̄}) ×_Z W` of a morphism `k : W ⟶ Z` to the strict
henselization of `Z` at a geometric point `z̄`. -/
abbrev strictHenselizationPullback {Z : Scheme.{u}} (hZ : B.Contains Z) (z : GeometricPoint Z)
    {W : Scheme.{u}} (k : W ⟶ Z) : Scheme.{u} :=
  pullback (strictHenselizationToBase B Z hZ z) k

variable {X S Y T : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S)
  (x : GeometricPoint X) {h : Y ⟶ X} {e : Y ⟶ T} {g : T ⟶ S}

/-- The canonical morphism `Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T` attached to a
cartesian square with `h : Y ⟶ X`, `e : Y ⟶ T` and `g : T ⟶ S`: it is the morphism of strict
henselizations on the first factor and `e` on the second. -/
def strictHenselizationPullbackMap (sq : IsPullback h e f g) :
    strictHenselizationPullback B hX x h ⟶ strictHenselizationPullback B hS (x.map f) g :=
  pullback.lift
    (pullback.fst (strictHenselizationToBase B X hX x) h ≫
      strictHenselizationSquareMap B hX hS f x)
    (pullback.snd (strictHenselizationToBase B X hX x) h ≫ e)
    (by
      rw [Category.assoc, strictHenselizationSquareMap_comp, Category.assoc, ← sq.w,
        ← Category.assoc, ← Category.assoc, pullback.condition])

@[simp]
lemma strictHenselizationPullbackMap_comp_fst (sq : IsPullback h e f g) :
    strictHenselizationPullbackMap B hX hS f x sq ≫
        pullback.fst (strictHenselizationToBase B S hS (x.map f)) g =
      pullback.fst (strictHenselizationToBase B X hX x) h ≫
        strictHenselizationSquareMap B hX hS f x :=
  pullback.lift_fst _ _ _

@[simp]
lemma strictHenselizationPullbackMap_comp_snd (sq : IsPullback h e f g) :
    strictHenselizationPullbackMap B hX hS f x sq ≫
        pullback.snd (strictHenselizationToBase B S hS (x.map f)) g =
      pullback.snd (strictHenselizationToBase B X hX x) h ≫ e :=
  pullback.lift_snd _ _ _

/-- **Stacks Project, Tag 0F00**, the base change step of its proof. In a cartesian square with
`h : Y ⟶ X`, `e : Y ⟶ T` and `g : T ⟶ S`, the canonical morphism
`Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T` is a base change of the morphism of
strict henselizations `Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})`. -/
@[stacks 0F00 "the identity `Spec(O^sh_{X,x̄}) ×_X Y = Spec(O^sh_{S,f(x̄)}) ×_S T`-base-change of
`Spec(O^sh_{X,x̄}) ⟶ Spec(O^sh_{S,f(x̄)})` of the source's last sentence, and nothing else. The
tag's conclusion `f⁻¹ g_* F = h_* e⁻¹ F` is NOT asserted here or in
`globalSectionsIso_strictHenselizationPullback` below: the source obtains it from this
identification together with Tag 03PU and Tag 03Q9, and Tag 03Q9 for sheaves of sets is not
available in the library (the only form of it present is restricted to a base which is already
the spectrum of a strictly henselian local ring)."]
theorem isPullback_strictHenselizationPullbackMap (sq : IsPullback h e f g) :
    IsPullback (pullback.fst (strictHenselizationToBase B X hX x) h)
      (strictHenselizationPullbackMap B hX hS f x sq)
      (strictHenselizationSquareMap B hX hS f x)
      (pullback.fst (strictHenselizationToBase B S hS (x.map f)) g) :=
  isPullback_baseChange_of_isPullback sq (strictHenselizationSquareMap_comp B hX hS f x)
    (IsPullback.of_hasPullback (strictHenselizationToBase B X hX x) h)
    (IsPullback.of_hasPullback (strictHenselizationToBase B S hS (x.map f)) g)
    (strictHenselizationPullbackMap_comp_fst B hX hS f x sq)
    (strictHenselizationPullbackMap_comp_snd B hX hS f x sq)

/-- The canonical morphism `Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T` is
quasi-compact: it is a base change of a morphism of affine schemes. -/
instance quasiCompact_strictHenselizationPullbackMap (sq : IsPullback h e f g) :
    QuasiCompact (strictHenselizationPullbackMap B hX hS f x sq) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_strictHenselizationPullbackMap B hX hS f x sq)
    (inferInstanceAs (QuasiCompact (strictHenselizationSquareMap B hX hS f x)))

/-- **Stacks Project, Tag 0F00**, the application of Tag 0A3H in its proof. If the morphism of
strict henselizations at a geometric point `x̄` of `X` is flat with geometrically connected
fibres, then in a cartesian square the global sections of a sheaf of sets on the small étale
site of `Spec(O^sh_{S,f(x̄)}) ×_S T` are the global sections of its inverse image on the small
étale site of `Spec(O^sh_{X,x̄}) ×_X Y`, naturally in the sheaf. -/
@[stacks 0F00 "the application of Tag 0A3H to the morphism
`Spec(O^sh_{X,x̄}) ×_X Y ⟶ Spec(O^sh_{S,f(x̄)}) ×_S T` with which the source's proof concludes,
and nothing else. The tag's conclusion `f⁻¹ g_* F = h_* e⁻¹ F` is NOT asserted: the source
reads the two sides of this identification as the stalks at `x̄` of `f⁻¹ g_* F` and of
`h_* e⁻¹ F` by Tag 03Q9 and concludes by Tag 03PU, and Tag 03Q9 for sheaves of sets is absent
from the library. Flatness of the morphism of strict henselizations, which Tag 0A3H needs and
the source leaves implicit in the flatness of `f`, is the declared hypothesis `hflat`."]
def globalSectionsIso_strictHenselizationPullback (sq : IsPullback h e f g)
    (hflat : Flat (strictHenselizationSquareMap B hX hS f x))
    (hconn : GeometricallyConnected (strictHenselizationSquareMap B hX hS f x)) :
    Sheaf.Γ (smallEtaleTopology (strictHenselizationPullback B hS (x.map f) g))
        (Type (max (u + 1) v)) ≅
      smallEtaleInverseImage.{u, v} (strictHenselizationPullbackMap B hX hS f x sq) ⋙
        Sheaf.Γ (smallEtaleTopology (strictHenselizationPullback B hX x h))
          (Type (max (u + 1) v)) := by
  have hpb := isPullback_strictHenselizationPullbackMap B hX hS f x sq
  have : Flat (strictHenselizationPullbackMap B hX hS f x sq) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hflat
  have : GeometricallyConnected (strictHenselizationPullbackMap B hX hS f x sq) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb hconn
  exact globalSectionsSmallEtaleInverseImageIso.{u, v}
    (strictHenselizationPullbackMap B hX hS f x sq)
    (universally_isQuotientMap_of_flat_quasiCompact
      (strictHenselizationPullbackMap B hX hS f x sq))

end StrictHenselizationPullback

end Stacks.EtaleCohomology

end
