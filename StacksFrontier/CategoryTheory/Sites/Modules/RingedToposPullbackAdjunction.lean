module

public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback of modules is left adjoint to pushforward

Let `(f, f^♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi or ringed
sites, let `F` be a sheaf of `O_C`-modules and let `G` be a sheaf of `O_D`-modules.
This file records the canonical bijection

`Hom_{O_C}(f^* G, F) = Hom_{O_D}(G, f_* F)`

of Stacks 03D7, that is, the statement that `f^*` is left adjoint to `f_*`.

## Main results

* `AlgebraicGeometry.RingedToposSiteHom.homEquivModules`: the canonical bijection of
  hom-sets displayed in the source.
* `AlgebraicGeometry.RingedToposSiteHom.homEquivModules_naturality_left` and
  `AlgebraicGeometry.RingedToposSiteHom.homEquivModules_naturality_right`: the bijection is
  natural in each of the two modules, which is the content of the source's "canonical".
* `SheafOfModules.pullbackPushforwardAdjunction` is cited for the ringed-site case; the
  `add_to_stacks` command below attaches the tag to it.

## Implementation notes

The two clauses of the source are the ringed-site case and the ringed-topos case. The
ringed-site case is exactly Mathlib's `SheafOfModules.pullbackPushforwardAdjunction`, the
adjunction attached to a continuous functor of sites together with a morphism of sheaves of
rings, and it is cited rather than restated. The ringed-topos case is obtained from it by
specialising to the structure map `fSharpRing` of a morphism of ringed topoi, which is what
`RingedToposSiteHom.pullbackTopos` and `RingedToposSiteHom.pushforwardTopos` are defined from;
that specialisation is `RingedToposSiteHom.pullbackPushforwardAdjunctionTopos`, which lives
alongside those two functors, and this file reads the displayed bijection off it.

Following `RingedToposSiteHom`, the geometric morphism is presented by a continuous functor
between the underlying sites rather than by an arbitrary adjoint pair of functors between
the topoi, and the two ringed topoi share the universe of the sections of their structure
sheaves; this is the generality in which Mathlib's pullback of sheaves of modules exists.
The source's bijection is a bijection of hom-sets, so it is recorded as an `Equiv` together
with its naturality in both variables, rather than only as the adjunction datum.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public section

open CategoryTheory

add_to_stacks 03D7 "ringed sites: the adjunction attached to a continuous functor of sites \
together with a morphism of sheaves of rings" SheafOfModules.pullbackPushforwardAdjunction

namespace AlgebraicGeometry.RingedToposSiteHom

universe w

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 03D7**, the displayed bijection. For a sheaf `G` of `O_Y`-modules and a sheaf
`F` of `O_X`-modules, morphisms `f^* G ⟶ F` of `O_X`-modules correspond bijectively to
morphisms `G ⟶ f_* F` of `O_Y`-modules. -/
@[stacks 03D7 "the canonical bijection `Hom_{O_X}(f^* G, F) = Hom_{O_Y}(G, f_* F)`",
  sga "4 IV 13.4" "(a) 13.4.1"]
noncomputable def homEquivModules (f : RingedToposSiteHom X Y)
    (G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (f.pullbackTopos.obj G ⟶ F) ≃ (G ⟶ f.pushforwardTopos.obj F) :=
  (f.pullbackPushforwardAdjunctionTopos).homEquiv G F

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The bijection of `homEquivModules` is natural in the `O_Y`-module `G`. -/
theorem homEquivModules_naturality_left (f : RingedToposSiteHom X Y)
    {G G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (g : G' ⟶ G) (h : f.pullbackTopos.obj G ⟶ F) :
    f.homEquivModules G' F (f.pullbackTopos.map g ≫ h) = g ≫ f.homEquivModules G F h :=
  (f.pullbackPushforwardAdjunctionTopos).homEquiv_naturality_left g h

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The bijection of `homEquivModules` is natural in the `O_X`-module `F`. -/
theorem homEquivModules_naturality_right (f : RingedToposSiteHom X Y)
    {G : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    {F F' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : f.pullbackTopos.obj G ⟶ F) (k : F ⟶ F') :
    f.homEquivModules G F' (h ≫ k) =
      f.homEquivModules G F h ≫ f.pushforwardTopos.map k :=
  (f.pullbackPushforwardAdjunctionTopos).homEquiv_naturality_right h k

end AlgebraicGeometry.RingedToposSiteHom

end
