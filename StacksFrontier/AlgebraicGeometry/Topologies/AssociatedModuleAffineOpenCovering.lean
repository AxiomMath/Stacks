module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePropagation

/-!
# The objects of a site of schemes lying over an affine open of the base

Tag 03OJ considers a site `C` of schemes over `S` subject to four conditions, the second of which
says that every Zariski covering of an object of `C` is refined by a covering of `C`.  The fullness
clause of Descent, Lemma 0GN7 is reduced by
`Stacks.Sites.surjective_associatedModuleMap_of_property` to a local statement at any class of
objects through which the arrows cover, and the affine-base proof in
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFullness` takes that class to be the
objects with **affine underlying scheme** — a covering hypothesis which condition (2) does *not*
supply, because refining an affine Zariski covering produces objects that map into an affine open
without themselves being affine, and the regress does not terminate.

This file identifies the class that condition (2) *does* supply: the objects whose structure
morphism to `S` has image inside an affine open of `S`.  Refining the Zariski covering of an
object by the preimages of the affine opens of `S` lands in exactly this class, so the covering
hypothesis of the propagation lemmas is a *theorem* here, not a hypothesis.

## Main definitions

* `Stacks.Sites.OverAffineOpen`: the objects of the site whose structure morphism to `S` has image
  inside an affine open of `S`.

## Main results

* `Stacks.Sites.coverByImage_overAffineOpen_mem`: **the covering hypothesis of
  `Stacks.Sites.hom_ext_associatedModulePresheaf_of_property`, at the class
  `Stacks.Sites.OverAffineOpen`, from the Zariski-refinement condition of Tag 03OJ alone.**
* `Stacks.Sites.hom_ext_associatedModulePresheaf_of_zariskiRefinement`: two maps `Mᵃ ⟶ Nᵃ` which
  agree over the objects lying over an affine open of `S` are equal, with no covering hypothesis.
* `Stacks.Sites.surjective_associatedModuleMap_of_zariskiRefinement`: the fullness clause of
  Descent, Lemma 0GN7 for such a site, reduced to its local half at the objects lying over an
  affine open of `S`, with no covering hypothesis and no affineness assumption on `S`.

## Implementation notes

The Zariski covering fed to the refinement condition is the presieve of *all* open immersions into
the underlying scheme of the object whose image in `S` lies in an affine open, rather than the
family `CategoryTheory.Presieve.ofArrows` of the preimages of the affine opens.  Both are Zariski
coverings — the second is contained in the first, and joint surjectivity is inherited upwards
while the morphism property is inherited downwards — and the first can be destructed by taking
apart a conjunction, whereas a membership in `CategoryTheory.Presieve.ofArrows` at an arrow which
is not a variable cannot be case-split without an equality of objects of `Scheme`.

**The refinement hypothesis is the source's notion of refinement, and must stay so.**  It is
spelled `Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows`: each arrow of the
refining covering family *factors through* a member of `R`, which is the definition of refinement
in Sites, Definition 00VV.  It is **not** spelled `Presieve.map (toOver ⋙ Over.forget S) Q ≤ R`,
which by `CategoryTheory.Presieve.map_iff` asks that the image of each arrow of `Q` *be a member
of* `R` and is strictly stronger.  The difference is not cosmetic, and no automatic check can see
it: a development built on the membership form compiles and reads correctly unless the binder is
compared against the source.

Under the membership form the paragraph at the top of this file would be **false**.  The presieve
of open immersions with affine source is jointly surjective and consists of open immersions, hence
is a member of `AlgebraicGeometry.Scheme.zariskiPrecoverage`; feeding it to the hypothesis would
return a covering family of the site whose members have affine underlying schemes, and the
covering hypothesis of `Stacks.Sites.hom_ext_associatedModulePresheaf_of_isAffine` would be a
theorem rather than the obstruction described there.  Under the factoring form it is not: what
comes back is a factorization `l ≫ j = (toOver ⋙ Over.forget S).map q` through an open immersion
`j` with affine source, and nothing identifies that source with the underlying scheme of an object
of `C`, nor gives a morphism back from it — which is exactly the regress the top of this file
describes.

`Stacks.Sites.OverAffineOpen` survives the weakening, and that is why the reduction below is
stated at this class and not at the affine objects: its defining condition constrains only the
*image* of the structure morphism, and an image can only shrink along a factorization, so
factoring through an arrow whose image lies in an affine open puts the factored arrow's image
there too.

**What is not proved here.**  The local half.  At an object `X` lying over an affine open `V` of
`S` the component of `a : Mᵃ ⟶ Nᵃ` is a `Γ(T, 𝒪)`-linear map `Γ(T, g⁺M) → Γ(T, g⁺N)` on the
underlying scheme `T` of `X`, and the two steps that the affine-base argument of
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFullness` performs are still owed at
this class:

* producing a morphism of modules `g⁺M ⟶ g⁺N` out of that linear map.  Over an affine `T` this is
  `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq`; over a `T` which merely maps to
  the affine `V` the route is the composite of the pullback–pushforward adjunction with the
  tilde-`Γ` adjunction of `V`, which identifies `Hom(g⁺M, G)` with the `Γ(V, 𝒪)`-linear maps
  `Γ(V, M) → Γ(T, G)` for an **arbitrary** `G`.  This needs no quasi-coherence:
  `AlgebraicGeometry.tilde.adjunction` is `tilde.functor R ⊣ moduleSpecΓFunctor`, whose right
  adjoint `AlgebraicGeometry.moduleSpecΓFunctor : (Spec R).Modules ⥤ ModuleCat R` is global
  sections of an arbitrary module on `Spec R`, so no quasi-coherence is asked of `G` and no
  quasi-compactness of `g`.  What remains is the transport of that adjunction from `Spec Γ(V, 𝒪)`
  to the affine open `V` of `S` along `AlgebraicGeometry.IsAffineOpen.isoSpec`, together with the
  factorization of `g` through `V`; and then the agreement of the morphism it produces with the
  given linear map, which asks that `Γ(T, g⁺M)` be generated by the pullbacks of `Γ(V, M)`.  That
  last point is false on the nose —
  `AlgebraicGeometry.Scheme.Modules.span_range_pullbackSection_eq_top` holds only for `T` affine,
  and the module docstring of
  `StacksFrontier.AlgebraicGeometry.PullbackSections.AffineGeneration` records why — and holds only
  as a statement about sheaves on the site, after refining the Zariski covering of `T` by its
  affine opens.
* recognizing that morphism as the pullback of a single `φ : M ⟶ N`.  Over an affine base this is
  read off the component at an object with invertible structure morphism; over a general base the
  morphism `φ` is not a component of `a` at all, and has to be glued out of the local ones by the
  sheaf condition for `X ↦ Hom(g⁺M, g⁺N)` on `C`, which is
  `AlgebraicGeometry.isSheaf_presheafHom'` restricted along `toOver` by
  `Stacks.Sites.isSheaf_type_op_comp_of_precoverage`.

**The local half is still owed at this class, and Tag 0GN7 no longer waits on it.**  The span
statement of the first bullet is the obstruction, and it is not a gap in the apparatus:
`AlgebraicGeometry.Scheme.Modules.span_range_pullbackSection_eq_top` is stated at an affine open of
the *source* as well as of the base, and the module docstring of
`StacksFrontier.AlgebraicGeometry.PullbackSections.AffineGeneration` records that both of those
affineness hypotheses are needed.  So at an object lying over an affine open whose underlying
scheme is not affine, the morphism of modules produced from the component of `a` agrees with that
component on the image of `Γ(M, V)` and nothing forces agreement on `Γ(g⁺M, ⊤)`.
`StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleArbitraryBase` therefore closes Tag
0GN7 over an arbitrary base by a different route, at the objects whose underlying scheme **is**
affine — where `Stacks.AlgebraicGeometry.ModuleLimits.exists_hom_app_top_eq` gives the agreement on
the nose and the only thing missing is the gluing of the local morphisms, which it performs against
the presheaf of morphisms of pullbacks.  The price is that the covering hypothesis at the affine
objects is carried rather than derived, which is exactly what this file's `hZariski` was introduced
to avoid; the two reductions are therefore complementary and neither subsumes the other.

Accordingly no `@[stacks]` attribute is claimed: what is proved is the covering half of the
reduction, and the local half remains a named hypothesis.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- **The objects of a site of schemes over `S` lying over an affine open of `S`.**  An object `Y`
has this property when the image of the structure morphism of `toOver.obj Y` is contained in an
affine open of `S`; equivalently, when that structure morphism factors through an affine open.

This is the class of objects produced by refining a Zariski covering of an object by the
preimages of the affine opens of `S`, and so the class at which the Zariski-refinement condition
of Tag 03OJ supplies the covering hypothesis of
`Stacks.Sites.hom_ext_associatedModulePresheaf_of_property`. -/
public def OverAffineOpen : ObjectProperty C := fun Y =>
  ∃ V : S.Opens, IsAffineOpen V ∧ Set.range (toOver.obj Y).hom.base ⊆ (V : Set S)

/-- The presieve of open immersions into a scheme `T` whose composite with a morphism `g : T ⟶ S`
has image inside an affine open of `S`.  It is a Zariski covering of `T`:  all its members are
open immersions by construction, and it contains the inclusion of `g ⁻¹ᵁ V` for every affine open
`V` of `S`, which already covers `T` because the affine opens cover `S`. -/
public def affineOpenPreimagePresieve {T : Scheme.{u}} (g : T ⟶ S) : Presieve T :=
  fun ⦃_Z⦄ h => IsOpenImmersion h ∧
    ∃ V : S.Opens, IsAffineOpen V ∧ Set.range (h ≫ g).base ⊆ (V : Set S)

/-- The inclusion of the preimage of an open `V` of `S` is a member of
`Stacks.Sites.affineOpenPreimagePresieve` as soon as `V` is affine. -/
public theorem affineOpenPreimagePresieve_ι {T : Scheme.{u}} (g : T ⟶ S) {V : S.Opens}
    (hV : IsAffineOpen V) : affineOpenPreimagePresieve S g (g ⁻¹ᵁ V).ι := by
  refine ⟨inferInstance, V, hV, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact y.2

/-- **`Stacks.Sites.affineOpenPreimagePresieve` is a Zariski covering.** -/
public theorem affineOpenPreimagePresieve_mem_zariskiPrecoverage {T : Scheme.{u}} (g : T ⟶ S) :
    affineOpenPreimagePresieve S g ∈ Scheme.zariskiPrecoverage.{u} T := by
  refine ⟨fun x => ?_, fun {Z} h hh => hh.1⟩
  obtain ⟨V, hV, hxV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := g.base x) (U := ⊤) trivial
  refine ⟨Scheme.forget.obj (g ⁻¹ᵁ V).toScheme, Scheme.forget.map (g ⁻¹ᵁ V).ι,
    Presieve.map_map (F := Scheme.forget) (affineOpenPreimagePresieve_ι S g hV),
    ⟨⟨x, hxV⟩, rfl⟩⟩

variable (K : Precoverage C)

/-- **The arrows of a site of schemes over `S` which factor through an object lying over an affine
open of `S` cover, as soon as Zariski coverings are refined by coverings of the site.**  This is
the covering hypothesis of `Stacks.Sites.hom_ext_associatedModulePresheaf_of_property` at the
class `Stacks.Sites.OverAffineOpen`, proved from condition (2) of Tag 03OJ alone.

Refine `Stacks.Sites.affineOpenPreimagePresieve` of the structure morphism of `X` by a covering
family `Q` of the site.  Each member `q` of `Q` has `toOver.map q` an open immersion whose
composite with the structure morphism of `X` has image in an affine open `V` of `S`; that
composite is the structure morphism of the source of `q`, so the source lies over `V`, and `q`
factors through it. -/
public theorem coverByImage_overAffineOpen_mem
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (X : C) :
    Sieve.coverByImage (ObjectProperty.ι (OverAffineOpen S toOver)) X ∈ K.toGrothendieck X := by
  obtain ⟨Q, hQ, hQle⟩ := hZariski X (affineOpenPreimagePresieve S (toOver.obj X).hom)
    (affineOpenPreimagePresieve_mem_zariskiPrecoverage S (toOver.obj X).hom)
  refine K.toGrothendieck.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hQ)
  rintro Z f ⟨W, l, q, hq, rfl⟩
  obtain ⟨Z', k, j, ⟨-, V, hV, hVle⟩, hfac⟩ :=
    hQle _ _ (Presieve.map_map (F := toOver ⋙ Over.forget S) hq)
  have hw : (k ≫ j) ≫ (toOver.obj X).hom = (toOver.obj W).hom := by
    rw [hfac]; exact Over.w (toOver.map q)
  refine ⟨⟨⟨W, V, hV, ?_⟩, l, q, rfl⟩⟩
  rintro _ ⟨y, rfl⟩
  refine hVle ⟨k.base y, ?_⟩
  rw [← hw]
  rfl

variable (J : GrothendieckTopology C)

/-- **Two maps of associated presheaves of modules agreeing over the objects lying over an affine
open of `S` are equal**, on a site of schemes over `S` whose Zariski coverings are refined by
coverings of the site.  No covering hypothesis is carried:
`Stacks.Sites.coverByImage_overAffineOpen_mem` supplies it. -/
public theorem hom_ext_associatedModulePresheaf_of_zariskiRefinement
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S N toOver))
    {a b : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver}
    (h : ∀ X : C, OverAffineOpen S toOver X → a.app (op X) = b.app (op X)) :
    a = b :=
  hom_ext_associatedModulePresheaf_of_property S toOver K.toGrothendieck
    (OverAffineOpen S toOver) hN (coverByImage_overAffineOpen_mem S toOver K hZariski) h

/-- **The fullness clause of Descent, Lemma 0GN7 on a site of schemes over `S` whose Zariski
coverings are refined by coverings of the site, reduced to its local half at the objects lying
over an affine open of `S`.**  No covering hypothesis is carried and the base `S` is arbitrary;
the hypothesis `hlocal` is the local half, which is not proved in this tree — see the
implementation notes of this module for the two steps it still needs. -/
public theorem surjective_associatedModuleMap_of_zariskiRefinement
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : Presheaf.IsSheaf K.toGrothendieck (associatedPresheaf S N toOver))
    (hlocal : ∀ a : associatedModulePresheaf S M toOver ⟶ associatedModulePresheaf S N toOver,
      ∃ φ : M ⟶ N, ∀ X : C, OverAffineOpen S toOver X →
        (associatedModuleMap S toOver φ).app (op X) = a.app (op X)) :
    Function.Surjective fun φ : M ⟶ N => associatedModuleMap S toOver φ :=
  surjective_associatedModuleMap_of_property S toOver K.toGrothendieck
    (OverAffineOpen S toOver) hN (coverByImage_overAffineOpen_mem S toOver K hZariski) hlocal

end Stacks.Sites

end
