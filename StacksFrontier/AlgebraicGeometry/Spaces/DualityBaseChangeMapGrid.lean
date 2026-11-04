module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangeMap

/-!
# The base change maps of a `3 × 3` grid of Tor independent squares of algebraic spaces

Let `S` be a scheme and consider a commutative diagram of algebraic spaces over `S`

```
X'' --k'--> X' --k--> X
 |f''        |f'       |f
 v           v         v
Y'' --l'--> Y' --l--> Y
 |g''        |g'       |g
 v           v         v
Z'' --m'--> Z' --m--> Z
```

all of whose squares, labelled `A B / C D`, are cartesian, with `(f, l)`, `(g, m)`, `(f', l')`
and `(g', m')` Tor independent pairs. Write `γ_A, …, γ_D` for the base change maps of
Stacks 0E5D of the four squares
(`AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMap`), and `γ_{A+B}`,
`γ_{C+D}`, `γ_{A+C}`, `γ_{B+D}` for those of the four `2 × 1` and `1 × 2` rectangles, read through
the identifications `L(k ∘ k')^* = L(k')^* ∘ Lk^*` and `c = a ∘ b` of Stacks 0E5E and 0E5F.
[Stacks, Tag 0E5G] observes that the two transformations
`(k')^* ∘ k^* ∘ a ∘ b ⟶ a'' ∘ b'' ∘ (m')^* ∘ m^*`, namely `γ_{A+C} ∘ γ_{B+D}` and
`γ_{C+D} ∘ γ_{A+B}`, are equal.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMapPasteVert`: the map of
  Stacks 0E5D of the outer rectangle of two vertically stacked squares, read through the
  identifications `c ≅ a ∘ b` and `c' ≅ a' ∘ b'` of the right adjoints.
* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz`: the map of
  Stacks 0E5D of the outer rectangle of two horizontally adjacent squares, read through the
  identifications `L(g ∘ g')^* ≅ L(g')^* ∘ Lg^*` and `L(h ∘ h')^* ≅ L(h')^* ∘ Lh^*`.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMapPasteVert_app` and
  `quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz_app`: Stacks 0E5E and 0E5F in the
  form `γ_{B+D} = γ_D ∘ γ_B` and `γ_{A+B} = γ_A ∘ γ_B`.
* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMap_interchange`: the
  commutative square `γ_A ∘ γ_D = γ_D ∘ γ_A` with which the source concludes.
* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMap_grid`: **Stacks 0E5G**.

## References

* [Stacks Project, Tag 0E5G](https://stacks.math.columbia.edu/tag/0E5G)
* [Stacks Project, Tag 0E5D](https://stacks.math.columbia.edu/tag/0E5D)
* [Stacks Project, Tag 0E5E](https://stacks.math.columbia.edu/tag/0E5E)
* [Stacks Project, Tag 0E5F](https://stacks.math.columbia.edu/tag/0E5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

section Vertical

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'}
  {g' : Y' ⟶ Z'} {k : X' ⟶ X} {l : Y' ⟶ Y} {m : Z' ⟶ Z}
  (sqt : IsPullback k f' f l) (sqb : IsPullback l g' g m)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hZqs : IsAbsolutelyQuasiSeparated B S hS hZ Z.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hZ'qc : IsQuasiCompactSpace B S hS Z'.1) (hZ'qs : IsAbsolutelyQuasiSeparated B S hS hZ Z'.1)
  (hTt : TorIndependent X.2 Y'.2 Y.2 f.hom l.hom)
  (hTb : TorIndependent Y.2 Z'.2 Z.2 g.hom m.hom)

/-- The base change map `Lk^* ∘ c ⟶ c' ∘ Lm^*` (Stacks 0E5D) of the outer rectangle of two
vertically stacked squares, read through the identifications `a ∘ b ≅ c` and `a' ∘ b' ≅ c'` of
the right adjoints of `R(g ∘ f)_* = Rg_* ∘ Rf_*` and `R(g' ∘ f')_* = Rg'_* ∘ Rf'_*`: the map
`k^* ∘ a ∘ b ⟶ a' ∘ b' ∘ m^*` that Stacks 0E5E and 0E5G call the base change map of the
rectangle. -/
def quasicoherentDerivedRightAdjointBaseChangeMapPasteVert :
    (quasicoherentDerivedRightAdjoint hZ g hYqc hYqs hZqs ⋙
        quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs) ⋙
        quasicoherentDerivedModulePullback k ⟶
      quasicoherentDerivedModulePullback m ⋙
        (quasicoherentDerivedRightAdjoint hZ g' hY'qc hY'qs hZ'qs ⋙
          quasicoherentDerivedRightAdjoint hZ f'
            (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc)
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs) hY'qs) :=
  Functor.whiskerRight
      (RightAdjointBaseChange.rightAdjointCompIso (squareAdjF hZ hXqc hXqs hYqs)
        (squareAdjF hZ hYqc hYqs hZqs) (squareAdjF hZ hXqc hXqs hZqs)
        (quasicoherentDerivedPushforwardCompIso f g
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z.2 hZqs hYqc g.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y.2 hYqs g.hom)
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z.2 hZqs hXqc (f ≫ g).hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs
            (f ≫ g).hom))).hom
      (quasicoherentDerivedModulePullback k) ≫
    quasicoherentDerivedRightAdjointBaseChangeMap hZ (sqt.paste_vert sqb) hXqc hXqs hZqs
      hZ'qc hZ'qs (torIndependent_rectangle_vertical sqb hTt hTb) ≫
    Functor.whiskerLeft (quasicoherentDerivedModulePullback m)
      (RightAdjointBaseChange.rightAdjointCompIso
        (squareAdjF' hZ sqt hXqc hXqs hYqs hY'qc hY'qs)
        (squareAdjF' hZ sqb hYqc hYqs hZqs hZ'qc hZ'qs)
        (squareAdjF' hZ (sqt.paste_vert sqb) hXqc hXqs hZqs hZ'qc hZ'qs)
        (quasicoherentDerivedPushforwardCompIso f' g'
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
            (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc) f'.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs) f'.hom)
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z'.2 hZ'qs hY'qc g'.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g'.hom)
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z'.2 hZ'qs
            (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc) (f' ≫ g').hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs) (f' ≫ g').hom))).inv

/-- Stacks 0E5E in the form `γ_{top+bot} = γ_bot ∘ γ_top`: the base change map of the outer
rectangle, read through `c ≅ a ∘ b` and `c' ≅ a' ∘ b'`, is `γ_top` at `b K` followed by `a'` of
`γ_bot` at `K`. -/
theorem quasicoherentDerivedRightAdjointBaseChangeMapPasteVert_app (K) :
    (quasicoherentDerivedRightAdjointBaseChangeMapPasteVert hZ sqt sqb hXqc hXqs hYqc hYqs hZqs
        hY'qc hY'qs hZ'qc hZ'qs hTt hTb).app K =
      (quasicoherentDerivedRightAdjointBaseChangeMap hZ sqt hXqc hXqs hYqs hY'qc hY'qs hTt).app
          ((quasicoherentDerivedRightAdjoint hZ g hYqc hYqs hZqs).obj K) ≫
        (quasicoherentDerivedRightAdjoint hZ f'
          (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs) hY'qs).map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sqb hYqc hYqs hZqs hZ'qc hZ'qs
            hTb).app K) := by
  simp only [quasicoherentDerivedRightAdjointBaseChangeMapPasteVert, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    quasicoherentDerivedRightAdjointBaseChangeMap_vertical hZ sqt sqb hXqc hXqs hYqc hYqs hZqs
      hY'qc hY'qs hZ'qc hZ'qs hTt hTb K, Category.assoc, Functor.comp_obj, Iso.hom_inv_id_app,
    Category.comp_id, ← Functor.map_comp_assoc]
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

end Vertical

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {f'' : X'' ⟶ Y''} {g : X' ⟶ X} {g' : X'' ⟶ X'} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
  (sqr : IsPullback g f' f h) (sql : IsPullback g' f'' f' h')
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hX'qc : IsQuasiCompactSpace B S hS X'.1) (hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hY''qc : IsQuasiCompactSpace B S hS Y''.1)
  (hY''qs : IsAbsolutelyQuasiSeparated B S hS hZ Y''.1)
  (hTr : TorIndependent X.2 Y'.2 Y.2 f.hom h.hom)
  (hTl : TorIndependent X'.2 Y''.2 Y'.2 f'.hom h'.hom)

/-- The base change map `L(g ∘ g')^* ∘ a ⟶ a'' ∘ L(h ∘ h')^*` (Stacks 0E5D) of the outer
rectangle of two horizontally adjacent squares, read through the identifications
`L(g ∘ g')^* ≅ L(g')^* ∘ Lg^*` and `L(h ∘ h')^* ≅ L(h')^* ∘ Lh^*`: the map
`(g')^* ∘ g^* ∘ a ⟶ a'' ∘ (h')^* ∘ h^*` that Stacks 0E5F and 0E5G call the base change map of
the rectangle. -/
def quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz :
    quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs ⋙
        (quasicoherentDerivedModulePullback g ⋙ quasicoherentDerivedModulePullback g') ⟶
      (quasicoherentDerivedModulePullback h ⋙ quasicoherentDerivedModulePullback h') ⋙
        quasicoherentDerivedRightAdjoint hZ f''
          (isQuasiCompactSpace_of_isPullback hZ (sql.paste_horiz sqr) hXqc hYqs hY''qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ (sql.paste_horiz sqr) hXqs hY''qs)
          hY''qs :=
  Functor.whiskerLeft (quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs)
      (quasicoherentDerivedModulePullbackCompIso g' g).hom ≫
    quasicoherentDerivedRightAdjointBaseChangeMap hZ (sql.paste_horiz sqr) hXqc hXqs hYqs
      hY''qc hY''qs (torIndependent_rectangle_horizontal sqr hTr hTl) ≫
    Functor.whiskerRight (quasicoherentDerivedModulePullbackCompIso h' h).inv
      (quasicoherentDerivedRightAdjoint hZ f''
        (isQuasiCompactSpace_of_isPullback hZ (sql.paste_horiz sqr) hXqc hYqs hY''qc)
        (isAbsolutelyQuasiSeparated_of_isPullback hZ (sql.paste_horiz sqr) hXqs hY''qs) hY''qs)

/-- Stacks 0E5F in the form `γ_{left+right} = γ_left ∘ γ_right`: the base change map of the
outer rectangle, read through `L(g ∘ g')^* ≅ L(g')^* ∘ Lg^*` and
`L(h ∘ h')^* ≅ L(h')^* ∘ Lh^*`, is `L(g')^*` of `γ_right` at `K` followed by `γ_left` at
`Lh^* K`. -/
theorem quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz_app (K) :
    (quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz hZ sqr sql hXqc hXqs hYqs hY''qc
        hY''qs hTr hTl).app K =
      (quasicoherentDerivedModulePullback g').map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sqr hXqc hXqs hYqs hY'qc hY'qs
            hTr).app K) ≫
        (quasicoherentDerivedRightAdjointBaseChangeMap hZ sql hX'qc hX'qs hY'qs hY''qc
          hY''qs hTl).app ((quasicoherentDerivedModulePullback h).obj K) := by
  simp only [quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    quasicoherentDerivedRightAdjointBaseChangeMap_horizontal hZ sqr sql hXqc hXqs hYqs hX'qc
      hX'qs hY'qc hY'qs hY''qc hY''qs hTr hTl K, Category.assoc, Functor.comp_obj,
    Iso.hom_inv_id_app_assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end Horizontal

section Grid

variable {X X' X'' Y Y' Y'' Z Z' Z'' : AlgebraicSpaces B S hS}
  {f : X ⟶ Y} {f' : X' ⟶ Y'} {f'' : X'' ⟶ Y''} {g : Y ⟶ Z} {g' : Y' ⟶ Z'} {g'' : Y'' ⟶ Z''}
  {k : X' ⟶ X} {k' : X'' ⟶ X'} {l : Y' ⟶ Y} {l' : Y'' ⟶ Y'} {m : Z' ⟶ Z} {m' : Z'' ⟶ Z'}
  (sqA : IsPullback k' f'' f' l') (sqB : IsPullback k f' f l)
  (sqC : IsPullback l' g'' g' m') (sqD : IsPullback l g' g m)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hX'qc : IsQuasiCompactSpace B S hS X'.1) (hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
  (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hY''qc : IsQuasiCompactSpace B S hS Y''.1)
  (hY''qs : IsAbsolutelyQuasiSeparated B S hS hZ Y''.1)
  (hZqs : IsAbsolutelyQuasiSeparated B S hS hZ Z.1)
  (hZ'qc : IsQuasiCompactSpace B S hS Z'.1) (hZ'qs : IsAbsolutelyQuasiSeparated B S hS hZ Z'.1)
  (hZ''qc : IsQuasiCompactSpace B S hS Z''.1)
  (hZ''qs : IsAbsolutelyQuasiSeparated B S hS hZ Z''.1)
  (hTA : TorIndependent X'.2 Y''.2 Y'.2 f'.hom l'.hom)
  (hTB : TorIndependent X.2 Y'.2 Y.2 f.hom l.hom)
  (hTC : TorIndependent Y'.2 Z''.2 Z'.2 g'.hom m'.hom)
  (hTD : TorIndependent Y.2 Z'.2 Z.2 g.hom m.hom)

/-- The commutative square with which Stacks 0E5G concludes:
`γ_A ∘ γ_D = γ_D ∘ γ_A` as maps `(k')^* ∘ a' ∘ l^* ∘ b ⟶ a'' ∘ (l')^* ∘ b' ∘ m^*`, by
naturality of `γ_A`. -/
theorem quasicoherentDerivedRightAdjointBaseChangeMap_interchange (K) :
    (quasicoherentDerivedModulePullback k').map
        ((quasicoherentDerivedRightAdjoint hZ f' hX'qc hX'qs hY'qs).map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sqD hYqc hYqs hZqs hZ'qc hZ'qs
            hTD).app K)) ≫
      (quasicoherentDerivedRightAdjointBaseChangeMap hZ sqA hX'qc hX'qs hY'qs hY''qc hY''qs
        hTA).app ((quasicoherentDerivedRightAdjoint hZ g' hY'qc hY'qs hZ'qs).obj
          ((quasicoherentDerivedModulePullback m).obj K)) =
    (quasicoherentDerivedRightAdjointBaseChangeMap hZ sqA hX'qc hX'qs hY'qs hY''qc hY''qs
        hTA).app ((quasicoherentDerivedModulePullback l).obj
          ((quasicoherentDerivedRightAdjoint hZ g hYqc hYqs hZqs).obj K)) ≫
      (quasicoherentDerivedRightAdjoint hZ f''
          (isQuasiCompactSpace_of_isPullback hZ sqA hX'qc hY'qs hY''qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ sqA hX'qs hY''qs) hY''qs).map
        ((quasicoherentDerivedModulePullback l').map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sqD hYqc hYqs hZqs hZ'qc hZ'qs
            hTD).app K)) :=
  (quasicoherentDerivedRightAdjointBaseChangeMap hZ sqA hX'qc hX'qs hY'qs hY''qc hY''qs
    hTA).naturality _

/-- **Stacks 0E5G.**  Let `S` be a scheme and consider a commutative diagram

```
X'' --k'--> X' --k--> X
 |f''        |f'       |f
 v           v         v
Y'' --l'--> Y' --l--> Y
 |g''        |g'       |g
 v           v         v
Z'' --m'--> Z' --m--> Z
```

of quasi-compact and quasi-separated algebraic spaces over `S` whose squares `A B / C D` are
cartesian, with `(f, l)`, `(g, m)`, `(f', l')`, `(g', m')` Tor independent pairs. Let `a`, `a'`,
`a''`, `b`, `b'`, `b''` be the right adjoints of Stacks 0E55 for `f`, `f'`, `f''`, `g`, `g'`, `g''`
(`AlgebraicGeometry.Space.quasicoherentDerivedRightAdjoint`). Then the two transformations
`(k')^* ∘ k^* ∘ a ∘ b ⟶ a'' ∘ b'' ∘ (m')^* ∘ m^*` built from the base change maps (Stacks 0E5D)
of the rectangles, `γ_{A+C} ∘ γ_{B+D}` (columns) and `γ_{C+D} ∘ γ_{A+B}` (rows), are equal. Here
the maps of the rectangles are read through the identifications of Stacks 0E5E and 0E5F
(`quasicoherentDerivedRightAdjointBaseChangeMapPasteVert`,
`quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz`), and the equality is stated at every
object `K` of `D_QCoh(𝒪_Z)`.

Of the source's standing hypothesis that all nine spaces are quasi-compact and quasi-separated,
two parts are not assumed: `X''` inherits both properties from the cartesian squares, and
quasi-compactness of `Z` is not used. -/
@[stacks 0E5G]
theorem quasicoherentDerivedRightAdjointBaseChangeMap_grid (K) :
    (quasicoherentDerivedModulePullback k').map
        ((quasicoherentDerivedRightAdjointBaseChangeMapPasteVert hZ sqB sqD hXqc hXqs hYqc hYqs
          hZqs hY'qc hY'qs hZ'qc hZ'qs hTB hTD).app K) ≫
      (quasicoherentDerivedRightAdjointBaseChangeMapPasteVert hZ sqA sqC hX'qc hX'qs hY'qc hY'qs
        hZ'qs hY''qc hY''qs hZ''qc hZ''qs hTA hTC).app
          ((quasicoherentDerivedModulePullback m).obj K) =
    (quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz hZ sqB sqA hXqc hXqs hYqs hY''qc
        hY''qs hTB hTA).app
          ((quasicoherentDerivedRightAdjoint hZ g hYqc hYqs hZqs).obj K) ≫
      (quasicoherentDerivedRightAdjoint hZ f''
          (isQuasiCompactSpace_of_isPullback hZ (sqA.paste_horiz sqB) hXqc hYqs hY''qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ (sqA.paste_horiz sqB) hXqs hY''qs)
          hY''qs).map
        ((quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz hZ sqD sqC hYqc hYqs hZqs
          hZ''qc hZ''qs hTD hTC).app K) := by
  rw [quasicoherentDerivedRightAdjointBaseChangeMapPasteVert_app,
    quasicoherentDerivedRightAdjointBaseChangeMapPasteVert_app,
    quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz_app,
    quasicoherentDerivedRightAdjointBaseChangeMapPasteHoriz_app]
  · simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% quasicoherentDerivedRightAdjointBaseChangeMap_interchange hZ sqA sqD hX'qc
      hX'qs hYqc hYqs hY'qc hY'qs hY''qc hY''qs hZqs hZ'qc hZ'qs hTA hTD K]

end Grid

end AlgebraicGeometry.Space

end
