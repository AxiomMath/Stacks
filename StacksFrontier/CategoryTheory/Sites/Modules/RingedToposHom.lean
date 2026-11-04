module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedTopos
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Adjunction.Additive
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Morphisms of ringed topoi, and pushforward and pullback of their modules

A morphism of ringed topoi `(f, f^♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is a morphism of topoi
`f` together with a map of sheaves of rings `f^♯ : O_D ⟶ f_* O_C` (equivalently, by
adjunction, `f⁻¹ O_D ⟶ O_C`). `AlgebraicGeometry.RingedToposSiteHom` below presents the
geometric morphism by a continuous functor `u : D.C ⥤ C.C` between the underlying sites,
which is the `Stacks 01D3`-morphism of the associated *ringed sites*; `toToposHom` produces
the underlying morphism of topoi once `u` is a morphism of sites.

For such a morphism the pushforward and the pullback of sheaves of modules
(`Stacks 03D6`) are Mathlib's `SheafOfModules.pushforward` and `SheafOfModules.pullback`
for the induced map of sheaves of (not necessarily commutative) rings. The pullback is
characterised as the left adjoint of the pushforward, and `pullbackToposIso` identifies it
with the sheafification of the presheaf-level extension of scalars
`O_C ⊗_{f⁻¹ O_D} f⁻¹ G`, which is the formula of the source.

## Main definitions

* `AlgebraicGeometry.RingedToposSiteHom`: a morphism of ringed topoi, presented by a continuous
  functor between the underlying sites together with the structure map `O_D ⟶ f_* O_C`.
* `AlgebraicGeometry.RingedToposSiteHom.comp`: composition of morphisms of ringed topoi.
* `AlgebraicGeometry.RingedToposSiteHom.toToposHom`: the underlying morphism of topoi.
* `AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos`: pushforward of sheaves of modules.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`: pullback of sheaves of modules.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.pullbackPushforwardAdjunctionTopos`: the pullback is
  left adjoint to the pushforward.
* `AlgebraicGeometry.RingedToposSiteHom.pullbackToposIso`: the pullback is the sheafification of
  the presheaf pullback, i.e. of `O_C ⊗_{f⁻¹ O_D} f⁻¹ G`.
* `AlgebraicGeometry.RingedToposSiteHom.pushforwardTopos_additive` and
  `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_additive`: both functors are additive.

## Implementation notes

Mathlib's `SheafOfModules.pullback` is indexed by a *continuous functor* between the two
sites, not by an arbitrary geometric morphism, and it requires the two sheaves of rings and
the modules to live in one and the same universe `w`. Accordingly `RingedToposSiteHom` takes a
continuous functor as its geometric datum and the two ringed topoi share the universe `w` of
the sections of their structure sheaves, while the universes of the objects and the morphisms
of the two sites stay independent. The structure map is stated for sheaves of *commutative*
rings, as in the source, and `fSharpRing` forgets commutativity; the forgetful functor
commutes with precomposition by `u.op` on the nose, so no comparison isomorphism intervenes.

## References

* [Stacks, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u' v'' u'' w

namespace AlgebraicGeometry

/-- **Stacks 01D3, part (2).** A morphism of ringed topoi `X ⟶ Y`: a morphism of topoi
between the underlying topoi together with a map of sheaves of commutative rings
`O_Y ⟶ f_* O_X`.

The geometric morphism is presented by a continuous functor `u : Y.C ⥤ X.C` between the
underlying sites in the opposite direction, as in the source's convention for a morphism of
sites; `RingedToposSiteHom.toToposHom` produces the morphism of topoi itself as soon as `u` is a
morphism of sites. This is the generality in which the pullback of sheaves of modules of
Stacks 03D6 is available. -/
@[stacks 01D3 "part (2): morphisms of ringed topoi, with the geometric morphism presented by
a continuous functor between the underlying sites rather than by an arbitrary adjoint pair;
`RingedToposHom.toToposHom` produces the underlying morphism of topoi once that functor is a
morphism of sites"]
structure RingedToposSiteHom (X : RingedTopos.{v, u, w}) (Y : RingedTopos.{v', u', w}) where
  /-- The continuous functor between the underlying sites, in the opposite direction. -/
  u : Y.C ⥤ X.C
  /-- The functor `u` is continuous, so that it induces a pushforward on sheaves. -/
  [isContinuous : u.IsContinuous Y.J X.J]
  /-- The structure map `f^♯ : O_Y ⟶ f_* O_X` of sheaves of commutative rings. -/
  fSharp : Y.O ⟶ (u.sheafPushforwardContinuous CommRingCat.{w} Y.J X.J).obj X.O

attribute [instance] RingedToposSiteHom.isContinuous

namespace RingedToposSiteHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  {Z : RingedTopos.{v'', u'', w}}

/-- **Stacks 01D3, part (3).** Composition of morphisms of ringed topoi: the underlying
continuous functors compose, and the structure map is
`O_Z ⟶ g_* O_Y ⟶ g_* f_* O_X = (g ∘ f)_* O_X`, the last identification being the canonical
one of `CategoryTheory.Functor.sheafPushforwardContinuousComp`. -/
@[stacks 01D3 "part (3): composition of morphisms of ringed topoi"]
def comp (g : RingedToposSiteHom Y Z) (f : RingedToposSiteHom X Y) : RingedToposSiteHom X Z where
  u := g.u ⋙ f.u
  isContinuous := Functor.isContinuous_comp g.u f.u Z.J Y.J X.J
  fSharp := g.fSharp ≫ (g.u.sheafPushforwardContinuous CommRingCat.{w} Z.J Y.J).map f.fSharp ≫
    (Functor.sheafPushforwardContinuousComp g.u f.u CommRingCat.{w} Z.J Y.J X.J).hom.app X.O

section

variable [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The structure map `f^♯` of a morphism of ringed topoi, read on underlying presheaves of
not necessarily commutative rings. Forgetting commutativity commutes with precomposition by
`u.op` on the nose, so this is `f.fSharp` whiskered with `forget₂ CommRingCat RingCat`, with
no comparison isomorphism intervening. -/
def fSharpPresheaf (f : RingedToposSiteHom X Y) :
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w} Y.O).obj ⟶
      f.u.op ⋙ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O).obj :=
  Functor.whiskerRight f.fSharp.hom (forget₂ CommRingCat.{w} RingCat.{w})

/-- The structure map `f^♯`, read as a map of sheaves of not necessarily commutative rings
`O_Y ⟶ f_* O_X`. -/
def fSharpRing (f : RingedToposSiteHom X Y) :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w} Y.O ⟶
      (f.u.sheafPushforwardContinuous RingCat.{w} Y.J X.J).obj
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) :=
  ObjectProperty.homMk f.fSharpPresheaf

/-- **Stacks 03D6, part (1).** The pushforward of sheaves of modules along a morphism of
ringed topoi: the underlying sheaf of abelian groups is the direct image `f_* F`, and the
module structure is restriction of scalars along `f^♯ : O_Y ⟶ f_* O_X`. -/
@[stacks 03D6 "part (1): pushforward of sheaves of modules along a morphism of ringed topoi,
presented by a morphism of the underlying sites", sga "4 Vbis 1.3.6" "special case"]
def pushforwardTopos (f : RingedToposSiteHom X Y) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w} Y.O) :=
  SheafOfModules.pushforward.{w}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, w} X.O)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', w} Y.O) f.fSharpRing

/-- The pushforward of sheaves of modules is additive: on underlying presheaves of modules
it is precomposition with `u.op`, which is additive on the nose. -/
instance pushforwardTopos_additive (f : RingedToposSiteHom X Y) :
    (f.pushforwardTopos).Additive where
  map_add := by intros; rfl

end

section Pullback

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The presheaf pushforward has a left adjoint by the general free-presheaf construction
applied to the canonical structure map. -/
instance presheafPushforward_isRightAdjoint (f : RingedToposSiteHom X Y) :
    (PresheafOfModules.pushforward.{w} f.fSharpRing.hom).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (PresheafOfModules.pullbackObjIsDefined_eq_top f.fSharpPresheaf)

/-- **Stacks 03D6, part (2).** The pullback of sheaves of modules along a morphism of ringed
topoi, characterised as the left adjoint of the pushforward. By `pullbackToposIso` it is the
sheafification of `O_X ⊗_{f⁻¹ O_Y} f⁻¹ G`, which is the formula of the source. -/
@[stacks 03D6 "part (2): pullback of sheaves of modules along a morphism of ringed topoi,
presented by a morphism of the underlying sites, both of which are small in the universe of
the sections of the structure sheaves; characterised as the left adjoint of the pushforward
and identified with the sheafification of `O_X ⊗_{f⁻¹ O_Y} f⁻¹ G` in `pullbackToposIso`",
  ega "0 4.3.1" "Ψ* functor", sga "4 IV 13.2.2" "commutative O, sites"]
def pullbackTopos (f : RingedToposSiteHom X Y) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
      SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  SheafOfModules.pullback.{w}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) f.fSharpRing

/-- The pullback of sheaves of modules is left adjoint to the pushforward. -/
@[stacks 03D7 "ringed topoi, with the geometric morphism presented by a continuous functor
between the underlying sites and the two structure sheaves sharing the universe of their
sections", sga "4 IV 13.4" "(a) 13.4.1"]
def pullbackPushforwardAdjunctionTopos (f : RingedToposSiteHom X Y) :
    f.pullbackTopos ⊣ f.pushforwardTopos :=
  SheafOfModules.pullbackPushforwardAdjunction.{w}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) f.fSharpRing

instance (f : RingedToposSiteHom X Y) : (f.pullbackTopos).IsLeftAdjoint :=
  (f.pullbackPushforwardAdjunctionTopos).isLeftAdjoint

/-- The pullback of sheaves of modules is additive, being a left adjoint of the additive
functor `pushforwardTopos`. -/
instance pullbackTopos_additive (f : RingedToposSiteHom X Y) : (f.pullbackTopos).Additive :=
  Adjunction.left_adjoint_additive f.pullbackPushforwardAdjunctionTopos

/-- The pullback of a sheaf of modules is the sheafification of the presheaf-level extension
of scalars along `f^♯`, that is, of `O_X ⊗_{f⁻¹ O_Y} f⁻¹ G`. -/
def pullbackToposIso (f : RingedToposSiteHom X Y) :
    f.pullbackTopos ≅ SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⋙
      PresheafOfModules.pullback.{w}
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
        (S := (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) f.fSharpPresheaf ⋙
        PresheafOfModules.sheafification
          (R₀ := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
          (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) :=
  SheafOfModules.pullbackIso.{w}
    (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    (S := Stacks.SheafOfModules.Tensor.ringSheaf Y.O) f.fSharpRing

/-- The morphism of topoi underlying a morphism of ringed topoi, given that the underlying
continuous functor is a morphism of sites (Stacks 00XC). -/
def toToposHom (f : RingedToposSiteHom X Y) (h : f.u.IsMorphismOfSites Y.J X.J) :
    MorphismOfTopoi X.Topos Y.Topos :=
  h.morphismOfTopoi

end Pullback

end RingedToposSiteHom

end AlgebraicGeometry
