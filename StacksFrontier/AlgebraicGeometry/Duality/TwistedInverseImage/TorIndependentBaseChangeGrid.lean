module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangePasteHoriz
public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangePasteVert

/-!
# The base change maps of the twisted inverse image on a grid of four squares

Consider a commutative diagram

```
X'' --k'--> X' --k--> X
 |          |         |
f''         f'        f
 v          v         v
Y'' --l'--> Y' --l--> Y
 |          |         |
g''         g'        g
 v          v         v
Z'' --m'--> Z' --m--> Z
```

of quasi-compact and quasi-separated schemes in which the four squares `A` (top left),
`B` (top right), `C` (bottom left) and `D` (bottom right) are cartesian, and `(f, l)`, `(g, m)`,
`(f', l')`, `(g', m')` are Tor independent pairs. Let `a, a', a''` and `b, b', b''` be the
right adjoints of `Rf_*, Rf'_*, Rf''_*` and `Rg_*, Rg'_*, Rg''_*` on `D_QCoh`
([Stacks, Tag 0A9E]) and `γ_A, γ_B, γ_C, γ_D` the base change maps of the squares
([Stacks, Tag 0AA6]). The base change maps of the four rectangles of two squares are
`γ_{A+B} = γ_A ∘ γ_B`, `γ_{C+D} = γ_C ∘ γ_D` ([Stacks, Tag 0ATR]) and `γ_{A+C} = γ_C ∘ γ_A`,
`γ_{B+D} = γ_D ∘ γ_B` ([Stacks, Tag 0ATQ]), the right adjoints of `R(f ≫ g)_*`, … being
identified with `b ⋙ a`, … by [Stacks, Tag 0ATX]. [Stacks, Tag 0ATS] observes that the two
resulting transformations

```
L(k')^* Lk^* a b ⟶ a'' b'' L(m')^* Lm^*,
```

`γ_{A+C} ∘ γ_{B+D} = γ_C ∘ γ_A ∘ γ_D ∘ γ_B` and `γ_{C+D} ∘ γ_{A+B} = γ_C ∘ γ_D ∘ γ_A ∘ γ_B`, agree:
this is the interchange law for `γ_A` and `γ_D`, which act on disjoint parts of the composite.

## Main results

* `Stacks.Duality.torIndependentTwistedInverseImageBaseChange_grid_interchange_app` — the
  interchange step `γ_C ∘ γ_A ∘ γ_D ∘ γ_B = γ_C ∘ γ_D ∘ γ_A ∘ γ_B`.
* `Stacks.Duality.twistedInverseImageBaseChangeMap_grid_app` — [Stacks, Tag 0ATS]: the vertical
  rectangles and the horizontal rectangles give the same transformation.

## References

* [Stacks Project, Tag 0ATS](https://stacks.math.columbia.edu/tag/0ATS)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {X'' X' X Y'' Y' Y Z'' Z' Z : Scheme.{u}}
  [CompactSpace X''] [QuasiSeparatedSpace X''] [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y''] [QuasiSeparatedSpace Y'']
  [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z''] [QuasiSeparatedSpace Z''] [CompactSpace Z'] [QuasiSeparatedSpace Z']
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  {k' : X'' ⟶ X'} {k : X' ⟶ X} {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {l' : Y'' ⟶ Y'} {l : Y' ⟶ Y} {g'' : Y'' ⟶ Z''} {g' : Y' ⟶ Z'} {g : Y ⟶ Z}
  {m' : Z'' ⟶ Z'} {m : Z' ⟶ Z}

/-- **The interchange step of [Stacks, Tag 0ATS].** On the grid of four Tor independent
cartesian squares, the two composites `γ_C ∘ γ_A ∘ γ_D ∘ γ_B` and `γ_C ∘ γ_D ∘ γ_A ∘ γ_B`
`L(k')^* Lk^* a(b(K)) ⟶ a''(b''(L(m')^* Lm^* K))` agree, because `γ_A` is natural with respect
to `γ_D`. -/
theorem torIndependentTwistedInverseImageBaseChange_grid_interchange_app
    (sqA : IsPullback k' f'' f' l') (sqB : IsPullback k f' f l)
    (sqC : IsPullback l' g'' g' m') (sqD : IsPullback l g' g m)
    (hB : TorIndependent f l) (hD : TorIndependent g m) (hA : TorIndependent f' l')
    (hC : TorIndependent g' m') (K : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedPullback' k').map
        ((torIndependentTwistedInverseImageBaseChange sqB hB).app
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K)) ≫
      (quasiCoherentDerivedPullback' k').map
        ((twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
          ((torIndependentTwistedInverseImageBaseChange sqD hD).app K)) ≫
      (torIndependentTwistedInverseImageBaseChange sqA hA).app
        ((twistedInverseImage g' (isQuasicoherent_homology_derivedPushforward_of_qcqs g')).obj
          ((quasiCoherentDerivedPullback' m).obj K)) ≫
      (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')).map
        ((torIndependentTwistedInverseImageBaseChange sqC hC).app
          ((quasiCoherentDerivedPullback' m).obj K)) =
    (quasiCoherentDerivedPullback' k').map
        ((torIndependentTwistedInverseImageBaseChange sqB hB).app
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K)) ≫
      (torIndependentTwistedInverseImageBaseChange sqA hA).app
        ((quasiCoherentDerivedPullback' l).obj
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K)) ≫
      (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')).map
        ((quasiCoherentDerivedPullback' l').map
          ((torIndependentTwistedInverseImageBaseChange sqD hD).app K)) ≫
      (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')).map
        ((torIndependentTwistedInverseImageBaseChange sqC hC).app
          ((quasiCoherentDerivedPullback' m).obj K)) := by
  have h := (torIndependentTwistedInverseImageBaseChange sqA hA).naturality
    ((torIndependentTwistedInverseImageBaseChange sqD hD).app K)
  simp only [Functor.comp_obj, Functor.comp_map] at h
  rw [reassoc_of% h]

/-- The diagram chase behind `Stacks.Duality.twistedInverseImageBaseChangeMap_grid_app`, with
every morphism a variable: both sides are the two composites of the interchange step, padded with
mutually inverse pairs. -/
private theorem grid_chase {C : Type*} [Category C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ P₁ : C}
    {p₁ : O₀ ⟶ O₁} {p₂ : O₁ ⟶ O₀} {β : O₀ ⟶ O₂} {δ : O₂ ⟶ O₃} {p₃ : O₃ ⟶ O₄} {p₄ : O₄ ⟶ O₃}
    {α : O₃ ⟶ O₅} {κ : O₅ ⟶ O₆} {p₅ : O₆ ⟶ O₇} {p₆ : O₇ ⟶ O₆}
    {q₁ : O₀ ⟶ O₈} {q₂ : O₈ ⟶ O₀} {α' : O₂ ⟶ P₁} {q₃ : P₁ ⟶ O₉} {q₄ : O₉ ⟶ P₁}
    {δ' : P₁ ⟶ O₅} {q₅ : O₆ ⟶ O₁₀} {q₆ : O₁₀ ⟶ O₆}
    (h₁ : p₁ ≫ p₂ = 𝟙 _) (h₃ : p₃ ≫ p₄ = 𝟙 _) (h₅ : p₅ ≫ p₆ = 𝟙 _) (k₁ : q₁ ≫ q₂ = 𝟙 _)
    (k₃ : q₃ ≫ q₄ = 𝟙 _) (k₅ : q₅ ≫ q₆ = 𝟙 _)
    (hint : β ≫ δ ≫ α ≫ κ = β ≫ α' ≫ δ' ≫ κ) :
    p₁ ≫ p₂ ≫ β ≫ δ ≫ p₃ ≫ p₄ ≫ α ≫ κ ≫ p₅ ≫ p₆ =
      q₁ ≫ q₂ ≫ β ≫ α' ≫ q₃ ≫ q₄ ≫ δ' ≫ κ ≫ q₅ ≫ q₆ := by
  rw [reassoc_of% h₁, reassoc_of% h₃, h₅, reassoc_of% k₁, reassoc_of% k₃, k₅]
  simpa only [Category.comp_id] using hint

/-- **[Stacks, Tag 0ATS].** Consider a commutative diagram
```
X'' --k'--> X' --k--> X
 |          |         |
f''         f'        f
 v          v         v
Y'' --l'--> Y' --l--> Y
 |          |         |
g''         g'        g
 v          v         v
Z'' --m'--> Z' --m--> Z
```
of quasi-compact and quasi-separated schemes in which all squares are cartesian and
`(f, l)`, `(g, m)`, `(f', l')`, `(g', m')` are Tor independent pairs. Let `a, a', a''`,
`b, b', b''` be the right adjoints of `Rf_*, Rf'_*, Rf''_*`, `Rg_*, Rg'_*, Rg''_*`
([Stacks, Tag 0A9E]); label the squares `A` (top left), `B` (top right), `C` (bottom left) and
`D` (bottom right). The base change maps (Equation 48.5.0.1 of [Stacks, Tag 0AA6]) of the four
rectangles made of two squares give two transformations
`L(k')^* Lk^* a b ⟶ a'' b'' L(m')^* Lm^*`, namely `γ_{A+C} ∘ γ_{B+D}` and `γ_{C+D} ∘ γ_{A+B}`, and
these are equal: for every `K ∈ D_QCoh(𝒪_Z)`,

* `γ_{A+C} ∘ γ_{B+D}` is `L(k')^* Lk^* a(b(K)) ≅ L(k')^* Lk^* c(K) ⟶ L(k')^* c'(Lm^* K) ⟶
  c''(L(m')^* Lm^* K) ≅ a''(b''(L(m')^* Lm^* K))`, with `c, c', c''` the right adjoints of
  `R(f ≫ g)_*, R(f' ≫ g')_*, R(f'' ≫ g'')_*` identified with `b ⋙ a`, … by
  [Stacks, Tag 0ATX];
* `γ_{C+D} ∘ γ_{A+B}` is `L(k')^* Lk^* a(b(K)) ≅ L(k' ≫ k)^* a(b(K)) ⟶ a''(L(l' ≫ l)^* b(K)) ⟶
  a''(b''(L(m' ≫ m)^* K)) ≅ a''(b''(L(m')^* Lm^* K))`, through the composition isomorphisms
  of derived pullback.

The base change maps of the rectangles are defined because their `ξ` are invertible
([Stacks, Tag 0ATR], [Stacks, Tag 0ATQ]). -/
@[stacks 0ATS]
theorem twistedInverseImageBaseChangeMap_grid_app
    (sqA : IsPullback k' f'' f' l') (sqB : IsPullback k f' f l)
    (sqC : IsPullback l' g'' g' m') (sqD : IsPullback l g' g m)
    (hB : TorIndependent f l) (hD : TorIndependent g m) (hA : TorIndependent f' l')
    (hC : TorIndependent g' m') (K : quasiCoherentDerivedCategory Z) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert sqB sqD hB hD
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert sqA sqC hA hC
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz sqB sqA hB hA
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz sqD sqC hD hC
    (quasiCoherentDerivedPullback' k').map ((quasiCoherentDerivedPullback' k).map
        ((twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).inv.app K)) ≫
      (quasiCoherentDerivedPullback' k').map
        ((twistedInverseImageBaseChangeMap k (f' ≫ g') (f ≫ g) m
          (isQuasicoherent_homology_derivedPushforward_of_qcqs k)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g'))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs m)
          (sqB.paste_vert sqD)).app K) ≫
      (twistedInverseImageBaseChangeMap k' (f'' ≫ g'') (f' ≫ g') m'
          (isQuasicoherent_homology_derivedPushforward_of_qcqs k')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g'))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f'' ≫ g''))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs m')
          (sqA.paste_vert sqC)).app ((quasiCoherentDerivedPullback' m).obj K) ≫
      (twistedInverseImageCompIso f'' g''
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (f'' ≫ g''))).hom.app
        ((quasiCoherentDerivedPullback' m').obj ((quasiCoherentDerivedPullback' m).obj K)) =
    (quasiCoherentDerivedPullbackCompIso k' k).hom.app
        ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj
            K)) ≫
      (twistedInverseImageBaseChangeMap (k' ≫ k) f'' f (l' ≫ l)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (k' ≫ k))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (l' ≫ l))
          (sqA.paste_horiz sqB)).app
        ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K) ≫
      (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')).map
        ((twistedInverseImageBaseChangeMap (l' ≫ l) g'' g (m' ≫ m)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (l' ≫ l))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs g'')
          (isQuasicoherent_homology_derivedPushforward_of_qcqs (m' ≫ m))
          (sqC.paste_horiz sqD)).app K) ≫
      (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')).map
        ((twistedInverseImage g'' (isQuasicoherent_homology_derivedPushforward_of_qcqs g'')).map
          ((quasiCoherentDerivedPullbackCompIso m' m).inv.app K)) := by
  rw [twistedInverseImageBaseChangeMap_paste_vert_app sqB sqD hB hD,
    twistedInverseImageBaseChangeMap_paste_vert_app sqA sqC hA hC,
    twistedInverseImageBaseChangeMap_paste_horiz_app sqB sqA hB hA,
    twistedInverseImageBaseChangeMap_paste_horiz_app sqD sqC hD hC]
  simp only [Functor.map_comp, Category.assoc]
  exact grid_chase
    (((quasiCoherentDerivedPullback' k').mapIso ((quasiCoherentDerivedPullback' k).mapIso
      ((twistedInverseImageCompIso f g _ _ _).app K))).inv_hom_id)
    (((quasiCoherentDerivedPullback' k').mapIso
      ((twistedInverseImageCompIso f' g' _ _ _).app _)).inv_hom_id)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _)
    (((twistedInverseImage f'' _).mapIso
      ((quasiCoherentDerivedPullbackCompIso l' l).app _)).hom_inv_id)
    (((twistedInverseImage f'' _).mapIso ((twistedInverseImage g'' _).mapIso
      ((quasiCoherentDerivedPullbackCompIso m' m).app K))).hom_inv_id)
    (torIndependentTwistedInverseImageBaseChange_grid_interchange_app sqA sqB sqC sqD hB hD hA hC
      K)

end Stacks.Duality
