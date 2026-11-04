module

public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleAffineOpenCovering

/-!
# The four conditions of Tag 03OJ pass to a slice of the site

Tag 03OJ considers a site `C` of schemes over a scheme `S`, presented here by a precoverage `K`
on `C` together with a functor `toOver : C ⥤ Over S`, subject to four conditions: (1) the
underlying category is a full subcategory of the schemes over `S`; (2) every Zariski covering of
an object is refined by a covering of the site; (3) `S/S` is an object of the site; (4) every
covering of the site becomes an fpqc covering of schemes.

The source's proof of the second assertion of the tag — that every quasi-coherent `𝒪`-module on
the site is an `Fᵃ` — is local on a covering of the final object: a module is presented on the
members of some covering family, the local statement is applied *on the slice at each member*,
and the resulting modules are glued by fpqc descent.  **The step that makes the local statement
applicable there is that the slice is again a site of the kind the tag considers**, over the
underlying scheme of the object sliced at, and that is what this file proves.

The slice at `X : C` is `Over X`, with the precoverage `K.comap (CategoryTheory.Over.forget X)` —
a family of arrows with target `T` covers in the slice exactly when it covers in `C` — and with
the canonical functor `Stacks.Sites.sliceToOver` into the schemes over the underlying scheme of
`X`.  All four conditions are inherited, over the new base `(toOver.obj X).left`:

* condition (1) is `Stacks.Sites.sliceToOver_full` together with the `Faithful` instance.  It is
  **not** an instance of `CategoryTheory.Over.post`'s own fullness instance, which would ask the
  functor `toOver ⋙ Over.forget S` to be full; that functor is not, since
  `CategoryTheory.Over.forget` is not.  Fullness of the slice functor uses the triangle over `S`
  instead: a morphism of schemes over the scheme of `X` is a morphism over `S`, because the
  structure morphism of `X` factors it, and then condition (1) for `toOver` applies;
* condition (2) is `Stacks.Sites.zariskiRefinement_sliceToOver`.  The underlying scheme of an
  object of the slice is the underlying scheme of its image in `C`, so the Zariski covering to be
  refined is already a Zariski covering of an object of `C`; the covering family that condition
  (2) returns consists of arrows of `C` with target in `C`, and every such arrow is an arrow of
  the slice, because its source acquires a structure morphism to `X` by composition.  That is the
  content of `CategoryTheory.Presieve.overEquiv`;
* condition (3) is `Stacks.Sites.sliceToOverObjIdIso`: the object `X` sliced at itself is the
  terminal object of the slice and its image is the identity of the new base.  **No hypothesis is
  needed** — condition (3) is free on a slice, whereas on `C` it is an assumption;
* condition (4) is `Stacks.Sites.fpqc_sliceToOver`, by the same transport as condition (2).

The site axioms travel with no work at all: `CategoryTheory.Precoverage.HasPullbacks` for
`K.comap (CategoryTheory.Over.forget X)` is already an instance, since
`CategoryTheory.Over.forget` creates pullbacks, and so is
`CategoryTheory.Precoverage.IsStableUnderBaseChange`.  Nothing is restated here for them, and
nothing need be.

## Main definitions

* `Stacks.Sites.sliceToOver`: the canonical functor from the slice of a site of schemes over `S`
  at an object `X` to the schemes over the underlying scheme of `X`.

## Main results

* `Stacks.Sites.sliceToOver_comp_forget` and `Stacks.Sites.map_sliceToOver_eq`: the functor to
  all schemes of the slice is the functor to all schemes of the site, read along the slice
  projection, and the image of a covering family of the slice is the image of its image.
* `Stacks.Sites.sliceToOver_full`: **condition (1) for the slice.**
* `Stacks.Sites.zariskiRefinement_sliceToOver`: **condition (2) for the slice.**
* `Stacks.Sites.sliceToOverObjIdIso`: **condition (3) for the slice**, unconditionally.
* `Stacks.Sites.fpqc_sliceToOver`: **condition (4) for the slice.**
* `Stacks.Sites.coverByImage_overAffineOpen_sliceToOver_mem`: the covering of
  `Stacks.Sites.coverByImage_overAffineOpen_mem` on the slice, as a consequence — the objects of
  the slice lying over an affine open of the *new* base cover, so the propagation engine of
  `StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModulePropagation` is available there.

## Implementation notes

No `@[stacks]` attribute is claimed.  Conditions (1)–(4) are the hypotheses of Tag 03OJ, and
their inheritance by a slice is a step of the tag's proof, not a statement of the tag.

The precoverage of the slice is `K.comap (CategoryTheory.Over.forget X)` and not a topology,
because conditions (2) and (4) are stated for the *generating* families of a precoverage;
`CategoryTheory.GrothendieckTopology.over_toGrothendieck_eq_toGrothendieck_comap_forget` says
that the topology this precoverage generates is the localization `K.toGrothendieck.over X` of the
topology of the site, so nothing is lost by presenting the slice this way.

## References

* [Stacks Project, Tag 03OJ](https://stacks.math.columbia.edu/tag/03OJ)
* [Stacks Project, Tag 00VV](https://stacks.math.columbia.edu/tag/00VV)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace Stacks.Sites

open _root_.AlgebraicGeometry

variable (S : Scheme.{u}) {C : Type (u + 1)} [Category.{u} C] (toOver : C ⥤ Over S)

/-- **The canonical functor of a slice of a site of schemes over `S`.**  An object of the slice at
`X : C` is an object of `C` together with a morphism to `X`; its image is the underlying scheme of
that object, regarded as a scheme over the underlying scheme of `X`. -/
public abbrev sliceToOver (X : C) : Over X ⥤ Over ((toOver.obj X).left) :=
  Over.post (toOver ⋙ Over.forget S)

/-- The functor to all schemes of the slice is the functor to all schemes of the site, read along
the slice projection.  This holds on the nose. -/
public theorem sliceToOver_comp_forget (X : C) :
    sliceToOver S toOver X ⋙ Over.forget ((toOver.obj X).left) =
      Over.forget X ⋙ (toOver ⋙ Over.forget S) :=
  rfl

/-- **Condition (1) of Tag 03OJ for a slice: the canonical functor of the slice is full.**

This is not `CategoryTheory.Over.post`'s fullness instance, which would need
`toOver ⋙ Over.forget S` to be full, and `CategoryTheory.Over.forget` is not.  A morphism
`φ` of the images is a morphism of schemes over the underlying scheme of `X`; composing with the
structure morphism of `X` makes it a morphism over `S`, so condition (1) for `toOver` produces a
morphism `f` of `C` above it, and faithfulness of `toOver` makes `f` a morphism of the slice. -/
public theorem sliceToOver_full [toOver.Full] [toOver.Faithful] (X : C) :
    (sliceToOver S toOver X).Full where
  map_surjective {A B} φ := by
    suffices h : ∀ ψ : (toOver.obj A.left).left ⟶ (toOver.obj B.left).left,
        ψ ≫ (toOver.map B.hom).left = (toOver.map A.hom).left →
        ∃ f : A ⟶ B, (toOver.map f.left).left = ψ by
      obtain ⟨f, hf⟩ := h φ.left (Over.w φ)
      exact ⟨f, by ext; exact hf⟩
    intro ψ hψ
    have hw : ψ ≫ (toOver.obj B.left).hom = (toOver.obj A.left).hom := by
      rw [← Over.w (toOver.map B.hom), ← Category.assoc, hψ]
      exact Over.w (toOver.map A.hom)
    obtain ⟨g, hg⟩ := toOver.map_surjective (Over.homMk ψ hw)
    have hg' : (toOver.map g).left = ψ := congrArg (·.left) hg
    refine ⟨Over.homMk g (toOver.map_injective ?_), hg'⟩
    ext
    simpa [hg'] using hψ

/-- **Condition (3) of Tag 03OJ for a slice, and it is free there**: the object `X` sliced at
itself has as image the identity of the new base.  That object is the terminal object of the
slice, `CategoryTheory.Over.mkIdTerminal`. -/
public def sliceToOverObjIdIso (X : C) :
    (sliceToOver S toOver X).obj (Over.mk (𝟙 X)) ≅ Over.mk (𝟙 ((toOver.obj X).left)) :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ 𝟙 ((toOver.obj X).left) = (toOver.map (𝟙 X)).left
    simp)

section Precoverage

variable (K : Precoverage C)

/-- **The image of a covering family of the slice, read in all schemes.**  The functor to all
schemes of the slice factors through the slice projection
(`Stacks.Sites.sliceToOver_comp_forget`), and the image of a presieve under a composite is the
image of its image. -/
public theorem map_sliceToOver_eq (X : C) (T : Over X) (Q : Presieve T) :
    Presieve.map (sliceToOver S toOver X ⋙ Over.forget ((toOver.obj X).left)) Q =
      Presieve.map (toOver ⋙ Over.forget S) (Presieve.map (Over.forget X) Q) :=
  le_antisymm
    (Presieve.map_le_iff_le_functorPullback.2 fun _ u (hu : Q u) =>
      Presieve.map_map (F := toOver ⋙ Over.forget S)
        (Presieve.map_map (F := Over.forget X) hu))
    (Presieve.map_le_iff_le_functorPullback.2
      (Presieve.map_le_iff_le_functorPullback.2 fun _ u (hu : Q u) =>
        Presieve.map_map (F := sliceToOver S toOver X ⋙ Over.forget ((toOver.obj X).left)) hu))

/-- **Condition (2) of Tag 03OJ for a slice: every Zariski covering of an object of the slice is
refined by a covering family of the slice.**

The underlying scheme of an object of the slice is the underlying scheme of its image in `C`, so
the given Zariski covering is a Zariski covering of an object of `C` and condition (2) for the
site returns a covering family `Q` of it.  Pulling `Q` back along the slice projection gives a
family of arrows of the slice — each arrow of `Q` has its source promoted to the slice by
composing with the structure morphism of its target — whose image in `C` is `Q` again
(`CategoryTheory.Presieve.map_functorPullback_overForget`), so it covers in the slice, and its
image downstairs is the image of `Q`. -/
public theorem zariskiRefinement_sliceToOver
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (X : C) (T : Over X)
    (R : Presieve (((sliceToOver S toOver X).obj T).left))
    (hR : R ∈ Scheme.zariskiPrecoverage.{u} (((sliceToOver S toOver X).obj T).left)) :
    ∃ Q : Presieve T, Q ∈ (K.comap (Over.forget X)) T ∧
      Presieve.map (sliceToOver S toOver X ⋙ Over.forget ((toOver.obj X).left)) Q ≤
        (Sieve.generate R).arrows := by
  obtain ⟨Q, hQ, hQle⟩ := hZariski T.left R hR
  refine ⟨Presieve.functorPullback (Over.forget X) Q, ?_, ?_⟩
  · rw [Precoverage.mem_comap_iff, Presieve.map_functorPullback_overForget]
    exact hQ
  · exact Presieve.map_le_iff_le_functorPullback.2
      fun _ u (hu : Q ((Over.forget X).map u)) =>
        hQle _ _ (Presieve.map_map (F := toOver ⋙ Over.forget S) hu)

/-- **Condition (4) of Tag 03OJ for a slice: every covering family of the slice becomes an fpqc
covering family of schemes.**  A covering family of the slice is a covering family of the site
read along the slice projection, and the two functors to all schemes agree. -/
public theorem fpqc_sliceToOver
    (hfpqc : ∀ (T : C) (Q : Presieve T), Q ∈ K T →
      Presieve.map (toOver ⋙ Over.forget S) Q ∈
        Scheme.fpqcPrecoverage.{u} ((toOver.obj T).left))
    (X : C) (T : Over X) (Q : Presieve T) (hQ : Q ∈ (K.comap (Over.forget X)) T) :
    Presieve.map (sliceToOver S toOver X ⋙ Over.forget ((toOver.obj X).left)) Q ∈
      Scheme.fpqcPrecoverage.{u} (((sliceToOver S toOver X).obj T).left) :=
  (map_sliceToOver_eq S toOver X T Q).symm ▸
    hfpqc T.left (Presieve.map (Over.forget X) Q) (Precoverage.mem_comap_iff.1 hQ)

/-- The arrows of the slice whose image factors through an object lying over an affine open of the
new base cover, as soon as the site satisfies condition (2).  This is
`Stacks.Sites.coverByImage_overAffineOpen_mem` on the slice, available because conditions (1)–(4)
are inherited. -/
public theorem coverByImage_overAffineOpen_sliceToOver_mem
    (hZariski : ∀ (T : C) (R : Presieve ((toOver.obj T).left)),
      R ∈ Scheme.zariskiPrecoverage.{u} ((toOver.obj T).left) →
        ∃ Q : Presieve T, Q ∈ K T ∧
          Presieve.map (toOver ⋙ Over.forget S) Q ≤ (Sieve.generate R).arrows)
    (X : C) (T : Over X) :
    Sieve.coverByImage
        (ObjectProperty.ι (OverAffineOpen ((toOver.obj X).left) (sliceToOver S toOver X))) T ∈
      (K.comap (Over.forget X)).toGrothendieck T :=
  coverByImage_overAffineOpen_mem ((toOver.obj X).left) (sliceToOver S toOver X)
    (K.comap (Over.forget X)) (zariskiRefinement_sliceToOver S toOver K hZariski X) T

end Precoverage

end Stacks.Sites

end
