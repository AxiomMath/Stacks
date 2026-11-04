module

public import StacksFrontier.CategoryTheory.Sites.ToposLocalization
public import StacksFrontier.CategoryTheory.Sites.SliceTopos.OverPushforward

/-! # Relocalizing a morphism of topoi: the morphism `f_c : E/U ⟶ D/V`

Let `f : E ⟶ D` be a morphism of topoi, let `V` be an object of `D`, let `U` be an object of `E`
and let `c : U ⟶ f⁻¹V`.  Stacks 04IN assembles, out of results already in the theory, the
commutative diagram of topoi

```
  E/U --j_U--> E
   |f_c        |f
  D/V --j_V--> D
```

together with three further assertions: that `f_c` factors as `f' ∘ j_{U/f⁻¹V}`, where `f'` is
the morphism of Stacks 04H1 (03CF) and `j_{U/f⁻¹V}` is the relocalization morphism of
Stacks 03EH; that

```
  (f_c)⁻¹(H --φ--> V) = (f⁻¹H ×_{f⁻¹φ, f⁻¹V, c} U ⟶ U) ;
```

and that these morphisms are compatible with further data `b : V' ⟶ V`, `a : U' ⟶ U`,
`c' : U' ⟶ f⁻¹V'` satisfying `c' ≫ f⁻¹b = a ≫ c`.

Stacks states the lemma for a morphism of *sites*, so that `U` and `V` are objects of the two
sites and `E/U`, `D/V` are the topoi `Sh(C/U)`, `Sh(D/V)` identified with the slices
`Sh(C)/h_U^#`, `Sh(D)/h_V^#` by Stacks 00Y1.  As in Stacks 04H1 (and for the same reason: the
statement is about topoi and does not refer to the underlying sites, Remark 03CJ) everything
below is proved for an arbitrary morphism of topoi and arbitrary objects `U`, `V` of the two
topoi, working in the slices `E/U` and `D/V` directly; the case of a morphism of sites is the
case `U = h_U^#`, `V = h_V^#`, so no identification is needed and no instance of 00Y1 is used.

The factorization `f_c = f' ∘ j_{U/f⁻¹V}` is how `f_c` is *defined* here, so it holds by
construction, as does the description of `(f_c)⁻¹`; that is faithful to Stacks, whose proof says
"this lemma proves itself".  The two squares are the substance, and they are proved the way
Stacks proves them: the first by combining the square of Stacks 04H1 with the identification
`j_{U/f⁻¹V}⁻¹ ∘ j_{f⁻¹V}⁻¹ = j_U⁻¹` (`toOverCompPullbackIso`, itself just uniqueness of right
adjoints applied to `Over.map c ⋙ Over.forget (f⁻¹V) = Over.forget U`), the second by the formal
pullback computation, which here becomes a Beck–Chevalley isomorphism for `Over.post` together
with `Over.pullbackComp` and the hypothesis `c' ≫ f⁻¹b = a ≫ c`.

## Main results

* `CategoryTheory.Over.pullbackCongr`: base change along equal morphisms agrees.
* `CategoryTheory.Over.postPullbackIso`: Beck–Chevalley for slices — if `F` preserves pullbacks
  then `Over.pullback g ⋙ Over.post F ≅ Over.post F ⋙ Over.pullback (F.map g)`.
* `CategoryTheory.toOverCompPullbackIso`: `j_{U/U'}⁻¹ ∘ j_{U'}⁻¹ = j_U⁻¹`, i.e.
  `toOver U' ⋙ Over.pullback a ≅ toOver U` for `a : U ⟶ U'`.
* `MorphismOfTopoi.overRelocalization`: the relocalization morphism of topoi
  `j_{U/U'} : E/U ⟶ E/U'`, whose inverse image is base change along `a : U ⟶ U'` (Stacks 03EH).
* `MorphismOfTopoi.relocalize` (Stacks 04IN): the morphism of topoi `f_c : E/U ⟶ D/V`, defined
  as `f' ∘ j_{U/f⁻¹V}`, and `relocalize_inverseImage_obj`, the description of `(f_c)⁻¹`.
* `MorphismOfTopoi.relocalizeInverseImageIso` (Stacks 04IN): commutativity of the first square,
  `j_U⁻¹ ∘ f⁻¹ = (f_c)⁻¹ ∘ j_V⁻¹`.
* `MorphismOfTopoi.relocalizeCompPullbackIso` (Stacks 04IN): commutativity of the last square,
  `(f_c)⁻¹ ∘ j_{U'/U}⁻¹ = j_{V'/V}⁻¹ ∘ (f_{c'})⁻¹`.

As in Stacks 04GZ, 04H0 and 04IR, the pushforward of a localization morphism is taken as data:
a general category with pullbacks need not have a right adjoint to `Over.pullback a` (in a topos
it does).

Tags covered: 04IN.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory CartesianMonoidalCategory

universe v v' u u'

variable {E : Type u} [Category.{v} E] {D : Type u'} [Category.{v'} D]

set_option backward.isDefEq.respectTransparency false in
/-- **Beck–Chevalley for slice categories.** If `F : E ⥤ D` preserves pullbacks then base change
commutes with `Over.post F`:
```
  Over.pullback g ⋙ Over.post F ≅ Over.post F ⋙ Over.pullback (F.map g) .
```
Concretely, `F` carries the fibre product `T ×_Y X` to the fibre product `F T ×_{F Y} F X`.

This is the "formal" step in the proof of Stacks 04IN: it is where the left exactness of the
inverse image `f⁻¹` of a morphism of topoi is used. -/
noncomputable def Over.postPullbackIso (F : E ⥤ D) [HasPullbacks E] [HasPullbacks D]
    [PreservesLimitsOfShape WalkingCospan F] {X Y : E} (g : X ⟶ Y) :
    Over.pullback g ⋙ Over.post F ≅ Over.post F ⋙ Over.pullback (F.map g) :=
  NatIso.ofComponents
    (fun T => Over.isoMk (PreservesPullback.iso F T.hom g)
      (by dsimp [Over.post]; simp [pullbackComparison_comp_snd]))
    (fun {T T'} _ => Over.OverMorphism.ext (by
      dsimp [Over.post]
      apply pullback.hom_ext <;> simp [pullbackComparison_comp_snd]))

/-- Base change along equal morphisms is the same functor.  Stated through uniqueness of right
adjoints rather than `eqToIso`, since `Over.pullback` carries a `HasPullbacksAlong` instance that
depends on the morphism, whereas `Over.map` does not. -/
noncomputable def Over.pullbackCongr [HasPullbacks E] {X Y : E} {g g' : X ⟶ Y} (h : g = g') :
    Over.pullback g ≅ Over.pullback g' :=
  Adjunction.rightAdjointUniq (congrArg Over.map h ▸ Over.mapPullbackAdj g)
    (Over.mapPullbackAdj g')

/-- **Stacks 03EH**, on inverse images: relocalizing and then restricting is restricting, i.e.
`j_{U/U'}⁻¹ ∘ j_{U'}⁻¹ = j_U⁻¹` where `j_{U/U'}⁻¹ = Over.pullback a` is base change along
`a : U ⟶ U'` and `j_U⁻¹ = toOver U`.

Both sides are right adjoints — of `Over.map a ⋙ Over.forget U'` and of `Over.forget U` — and
those two left adjoints are equal on the nose by `CategoryTheory.Over.mapForget_eq`, so this is
uniqueness of right adjoints. -/
noncomputable def toOverCompPullbackIso [CartesianMonoidalCategory E] [HasPullbacks E]
    {U U' : E} (a : U ⟶ U') :
    toOver U' ⋙ Over.pullback a ≅ toOver U :=
  Adjunction.rightAdjointUniq
    (Over.mapForget_eq a ▸ (Over.mapPullbackAdj a).comp (forgetAdjToOver U'))
    (forgetAdjToOver U)

end CategoryTheory

namespace MorphismOfTopoi

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

universe v v' u u'

variable {E : Type u} [Category.{v} E] {D : Type u'} [Category.{v'} D]

/-- **Stacks 03EH.** The relocalization morphism of topoi `j_{U/U'} : E/U ⟶ E/U'` attached to a
morphism `a : U ⟶ U'` of a topos `E`: its inverse image is base change along `a` and its lower
shriek is `Over.map a`.

Left exactness of the inverse image is free: `Over.pullback a` is the right adjoint of
`Over.map a`, hence preserves all limits.  The pushforward is taken as data. -/
@[simps inverseImage pushforward]
noncomputable def overRelocalization [HasPullbacks E] {U U' : E} (a : U ⟶ U')
    {p : Over U ⥤ Over U'} (adj : Over.pullback a ⊣ p) :
    MorphismOfTopoi (Over U) (Over U') where
  pushforward := p
  inverseImage := Over.pullback a
  adj := adj
  preservesFiniteLimits :=
    haveI := (Over.mapPullbackAdj a).rightAdjoint_preservesLimits
    ⟨fun _ _ _ => inferInstance⟩

variable (f : MorphismOfTopoi E D) [HasPullbacks E] [HasPullbacks D]

/-- **Stacks 04IN.** Let `f : E ⟶ D` be a morphism of topoi, `V` an object of `D`, `U` an object
of `E` and `c : U ⟶ f⁻¹V`.  The morphism of topoi `f_c : E/U ⟶ D/V` is the composition
```
  f_c = f' ∘ j_{U/f⁻¹V}
```
of the relocalization morphism `j_{U/f⁻¹V} : E/U ⟶ E/f⁻¹V` of Stacks 03EH with the morphism
`f' : E/f⁻¹V ⟶ D/V` of Stacks 04H1 (03CF); this factorization is Stacks 04IN's second
assertion, and holds here by construction.  Consequently
```
  (f_c)⁻¹ = Over.post f⁻¹ ⋙ Over.pullback c ,
```
see `relocalize_inverseImage_obj`. -/
@[stacks 04IN "the morphism of topoi f_c and the factorization f_c = f' ∘ j_{U/u(V)}"]
noncomputable def relocalize {V : D} {U : E} (c : U ⟶ f.inverseImage.obj V)
    {p : Over U ⥤ Over (f.inverseImage.obj V)} (adj : Over.pullback c ⊣ p) :
    MorphismOfTopoi (Over U) (Over V) :=
  (f.over V).comp (overRelocalization c adj)

/-- **Stacks 04IN**, the description of `(f_c)⁻¹`: an object `φ : H ⟶ V` of `D/V` is sent to the
fibre product
```
  (f⁻¹H ×_{f⁻¹φ, f⁻¹V, c} U ⟶ U) ,
```
the base change along `c` of `f⁻¹φ`. -/
@[stacks 04IN "the description of (f_c)^{-1} as a fibre product"]
lemma relocalize_inverseImage_obj {V : D} {U : E} (c : U ⟶ f.inverseImage.obj V)
    {p : Over U ⥤ Over (f.inverseImage.obj V)} (adj : Over.pullback c ⊣ p) (H : Over V) :
    (f.relocalize c adj).inverseImage.obj H =
      Over.mk (pullback.snd (f.inverseImage.map H.hom) c) :=
  rfl

variable [CartesianMonoidalCategory E] [CartesianMonoidalCategory D]

/-- **Stacks 04IN**, commutativity of the first square: `j_U⁻¹ ∘ f⁻¹ = (f_c)⁻¹ ∘ j_V⁻¹`, where
`j_U⁻¹ = toOver U` and `j_V⁻¹ = toOver V`.

The proof is the one Stacks gives: the square of Stacks 04H1 for `f'`, namely
`f⁻¹ ⋙ toOver (f⁻¹V) ≅ toOver V ⋙ (f')⁻¹`, is whiskered with the base change
`j_{U/f⁻¹V}⁻¹ = Over.pullback c`, and the left-hand side collapses by
`toOverCompPullbackIso`, the identity `j_{U/f⁻¹V}⁻¹ ∘ j_{f⁻¹V}⁻¹ = j_U⁻¹` of Stacks 03EH. -/
@[stacks 04IN "commutativity of the first square, on inverse images"]
noncomputable def relocalizeInverseImageIso {V : D} {U : E} (c : U ⟶ f.inverseImage.obj V)
    {p : Over U ⥤ Over (f.inverseImage.obj V)} (adj : Over.pullback c ⊣ p) :
    f.inverseImage ⋙ toOver U ≅ toOver V ⋙ (f.relocalize c adj).inverseImage :=
  Functor.isoWhiskerLeft f.inverseImage (toOverCompPullbackIso c).symm ≪≫
    Functor.isoWhiskerRight (f.inverseImageCompToOverIso V) (Over.pullback c)

/-- **Stacks 04IN**, commutativity of the last square: given `b : V' ⟶ V`, `a : U' ⟶ U` and
`c' : U' ⟶ f⁻¹V'` with `c' ≫ f⁻¹b = a ≫ c`, the square
```
  E/U' --j_{U'/U}--> E/U
   |f_{c'}            |f_c
  D/V' --j_{V'/V}--> D/V
```
commutes, i.e. `(f_c)⁻¹ ∘ j_{U'/U}⁻¹ = j_{V'/V}⁻¹ ∘ (f_{c'})⁻¹` on inverse images.

This is Stacks' equality
```
  f⁻¹H ×_{f⁻¹V, c} U ×_U U' = f⁻¹(H ×_V V') ×_{f⁻¹V', c'} U' ,
```
obtained here by Beck–Chevalley for `Over.post f⁻¹` (`Over.postPullbackIso`, which uses that
`f⁻¹` is left exact), the composition rule `Over.pullbackComp` for base change, and the
hypothesis `c' ≫ f⁻¹b = a ≫ c`. -/
@[stacks 04IN "commutativity of the last square, on inverse images"]
noncomputable def relocalizeCompPullbackIso {V V' : D} (b : V' ⟶ V) {U U' : E} (a : U' ⟶ U)
    (c : U ⟶ f.inverseImage.obj V) (c' : U' ⟶ f.inverseImage.obj V')
    (hc : c' ≫ f.inverseImage.map b = a ≫ c)
    {p : Over U ⥤ Over (f.inverseImage.obj V)} (adj : Over.pullback c ⊣ p)
    {p' : Over U' ⥤ Over (f.inverseImage.obj V')} (adj' : Over.pullback c' ⊣ p') :
    Over.pullback b ⋙ (f.relocalize c' adj').inverseImage ≅
      (f.relocalize c adj).inverseImage ⋙ Over.pullback a :=
  haveI := f.preservesFiniteLimits
  Functor.isoWhiskerRight (Over.postPullbackIso f.inverseImage b) (Over.pullback c') ≪≫
    Functor.isoWhiskerLeft (Over.post f.inverseImage)
      ((Over.pullbackComp c' (f.inverseImage.map b)).symm ≪≫ Over.pullbackCongr hc ≪≫
        Over.pullbackComp a c)

end MorphismOfTopoi
