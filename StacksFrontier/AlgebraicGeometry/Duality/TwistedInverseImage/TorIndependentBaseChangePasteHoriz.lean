module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangeMap

/-!
# The base change map of the twisted inverse image along two squares side by side

Consider a commutative diagram

```
X'' --g'--> X' --g--> X
 |          |         |
f''         f'        f
 v          v         v
Y'' --h'--> Y' --h--> Y
```

of quasi-compact and quasi-separated schemes in which both squares are cartesian, `f` and `h`
are Tor independent and `f'` and `h'` are Tor independent. Write `a`, `a'`, `a''` for the right
adjoints of `Rf_*`, `Rf'_*`, `Rf''_*` on `D_QCoh` ([Stacks, Tag 0A9E]), `k = g' ≫ g` and
`m = h' ≫ h`. The base change maps of [Stacks, Tag 0AA6] of the two squares compose to the base
change map of the outer rectangle ([Stacks, Tag 0ATR]): for `K ∈ D_QCoh(𝒪_Y)`,

```
Lk^* a(K) = L(g')^* Lg^* a(K) ⟶ L(g')^* a'(Lh^* K) ⟶ a''(L(h')^* Lh^* K) = a''(Lm^* K).
```

The base change map of the outer rectangle is defined once its transformation
`ξ : Rk_* ∘ a'' ⟶ a ∘ Rm_*` is invertible. This holds here because the derived base change map
`Lm^* ∘ Rf_* ⟶ Rf''_* ∘ Lk^*` of the rectangle is the pasting of those of the two squares,
which are invertible by Tor independence ([Stacks, Tag 08IB]).

## Main results

* `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz` — `ξ` of the
  outer rectangle is invertible.
* `Stacks.Duality.twistedInverseImageBaseChangeMap_paste_horiz_app` — [Stacks, Tag 0ATR].

## References

* [Stacks Project, Tag 0ATR](https://stacks.math.columbia.edu/tag/0ATR)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.CategoryTheory.BaseChange

variable {S S₁ S₂ T T₁ T₂ : Type*} [Category S] [Category S₁] [Category S₂] [Category T]
  [Category T₁] [Category T₂]
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lf₁ : S₁ ⥤ T₁} {Rf₁ : T₁ ⥤ S₁} {Lf₂ : S₂ ⥤ T₂} {Rf₂ : T₂ ⥤ S₂}
  (adjf : Lf ⊣ Rf) (adjf₁ : Lf₁ ⊣ Rf₁) (adjf₂ : Lf₂ ⊣ Rf₂)
  {G₁ : S ⥤ S₁} {G₂ : S₁ ⥤ S₂} {Go : S ⥤ S₂} {H₁ : T ⥤ T₁} {H₂ : T₁ ⥤ T₂} {Ho : T ⥤ T₂}
  {Lc₁ : S ⥤ T₁} {Lc₂ : S₁ ⥤ T₂} {Lco : S ⥤ T₂}
  (eg₁ : G₁ ⋙ Lf₁ ≅ Lc₁) (ef₁ : Lf ⋙ H₁ ≅ Lc₁) (eg₂ : G₂ ⋙ Lf₂ ≅ Lc₂) (ef₂ : Lf₁ ⋙ H₂ ≅ Lc₂)
  (ego : Go ⋙ Lf₂ ≅ Lco) (efo : Lf ⋙ Ho ≅ Lco)
  (cT : Go ≅ G₁ ⋙ G₂) (cB : H₁ ⋙ H₂ ≅ Ho)

/-- **The base change map of pushforward along pullback around two pasted squares is invertible
when those of the two squares are**, the outer one being their pasting. -/
theorem isIso_twoSquare_of_pullbackComparison_paste
    (hpc : PullbackComparisonPaste eg₁ ef₁ eg₂ ef₂ ego efo cT cB)
    [IsIso (twoSquare adjf adjf₁ eg₁ ef₁)]
    [IsIso (twoSquare adjf₁ adjf₂ eg₂ ef₂)] :
    IsIso (twoSquare adjf adjf₂ ego efo) := by
  have : ∀ M, IsIso ((twoSquare adjf adjf₂ ego efo).app M) := fun M => by
    change IsIso (map adjf adjf₂ ego efo M)
    rw [map_eq_of_pullbackComparison_paste adjf adjf₁ adjf₂ eg₁ ef₁ eg₂ ef₂ ego efo cT cB hpc M]
    have : IsIso (map adjf adjf₁ eg₁ ef₁ M) :=
      inferInstanceAs (IsIso ((twoSquare adjf adjf₁ eg₁ ef₁).app M))
    have : IsIso (map adjf₁ adjf₂ eg₂ ef₂ (H₁.obj M)) :=
      inferInstanceAs (IsIso ((twoSquare adjf₁ adjf₂ eg₂ ef₂).app (H₁.obj M)))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Stacks.CategoryTheory.BaseChange

namespace Stacks.Duality

/-- The isomorphism `Lh₁^* ≅ Lh₂^*` on `D_QCoh` attached to `h = h` has identity inverse. -/
private theorem quasiCoherentDerivedPullbackCongr_refl_inv {X Y : Scheme.{u}} (h : X ⟶ Y) :
    (quasiCoherentDerivedPullbackCongr (rfl : h = h)).inv = 𝟙 _ := by
  ext K
  rfl

section Square

variable {X' X Y' Y : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X]
  [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y'] [CompactSpace Y]
  [QuasiSeparatedSpace Y] {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- The derived base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` of a Tor independent cartesian
square of quasi-compact and quasi-separated schemes, in the shape of
`Stacks.CategoryTheory.BaseChange.twoSquare`, is invertible ([Stacks, Tag 08IB]). -/
theorem isIso_twoSquare_of_torIndependent (sq : IsPullback g' f' f g)
    (hTor : TorIndependent f g) :
    IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
      (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
      (quasiCoherentDerivedPullbackCompIso f' g)
      (quasiCoherentDerivedPullbackCompIso g' f ≪≫
        quasiCoherentDerivedPullbackCongr sq.w)) := by
  have h := isIso_quasiCoherentDerivedBaseChange_natTrans
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
    (isQuasicoherent_homology_derivedPushforward_of_qcqs g) sq hTor
  rwa [quasiCoherentDerivedBaseChange_eq_twoSquare] at h

end Square

variable {X'' X' X Y'' Y' Y : Scheme.{u}} [CompactSpace X''] [QuasiSeparatedSpace X'']
  [CompactSpace X'] [QuasiSeparatedSpace X'] [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y''] [QuasiSeparatedSpace Y''] [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  {g' : X'' ⟶ X'} {g : X' ⟶ X} {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y}
  {h' : Y'' ⟶ Y'} {h : Y' ⟶ Y}

/-- The derived base change map of the outer rectangle of two cartesian squares placed side by
side, each Tor independent, is invertible: it is the pasting of those of the two squares. -/
theorem isIso_twoSquare_of_paste_horiz (sqR : IsPullback g f' f h)
    (sqL : IsPullback g' f'' f' h') (hR : TorIndependent f h) (hL : TorIndependent f' h') :
    IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
      (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
      (quasiCoherentDerivedPullbackCompIso f'' (h' ≫ h))
      (quasiCoherentDerivedPullbackCompIso (g' ≫ g) f ≪≫
        quasiCoherentDerivedPullbackCongr (sqL.paste_horiz sqR).w)) := by
  have := isIso_twoSquare_of_torIndependent sqR hR
  have := isIso_twoSquare_of_torIndependent sqL hL
  exact Stacks.CategoryTheory.BaseChange.isIso_twoSquare_of_pullbackComparison_paste _
    (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f')) _ _ _ _ _ _ _ _ _
    (quasiCoherentPullbackComparisonPaste g f' f h g' f'' h' (g' ≫ g) (h' ≫ h) sqR.w sqL.w
      (sqL.paste_horiz sqR).w rfl rfl)

/-- **`ξ : Rk_* ∘ a'' ⟶ a ∘ Rm_*` of the outer rectangle is invertible**, for two cartesian
squares of quasi-compact and quasi-separated schemes placed side by side with `f`, `h` Tor
independent and `f'`, `h'` Tor independent; here `k = g' ≫ g` and `m = h' ≫ h`. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz
    (sqR : IsPullback g f' f h) (sqL : IsPullback g' f'' f' h') (hR : TorIndependent f h)
    (hL : TorIndependent f' h') :
    IsIso (twistedInverseImagePushforwardBaseChange (g' ≫ g) f'' f (h' ≫ h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (g' ≫ g))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (h' ≫ h)) (sqL.paste_horiz sqR)) := by
  have := isIso_twoSquare_of_paste_horiz sqR sqL hR hL
  rw [twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare]
  exact Stacks.CategoryTheory.BaseChange.isIso_rightAdjointSquare _ _ _ _ _ _ _ _

/-- **[Stacks, Tag 0ATR].** Consider a commutative diagram
```
X'' --g'--> X' --g--> X
 |          |         |
f''         f'        f
 v          v         v
Y'' --h'--> Y' --h--> Y
```
of quasi-compact and quasi-separated schemes in which both squares are cartesian, `f` and `h`
are Tor independent and `f'` and `h'` are Tor independent. Then the base change maps
(Equation 48.5.0.1 of [Stacks, Tag 0AA6]) of the two squares compose to the base change map of
the outer rectangle: with `k = g' ≫ g`, `m = h' ≫ h` and `a`, `a'`, `a''` the right adjoints of
`Rf_*`, `Rf'_*`, `Rf''_*`, for every `K ∈ D_QCoh(𝒪_Y)` the map `Lk^* a(K) ⟶ a''(Lm^* K)` of the
rectangle is

```
Lk^* a(K) = L(g')^* Lg^* a(K) ⟶ L(g')^* a'(Lh^* K) ⟶ a''(L(h')^* Lh^* K) = a''(Lm^* K),
```

the identifications being the composition isomorphisms of derived pullback. The base change map
of the rectangle is defined because its `ξ` is invertible,
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz`. -/
@[stacks 0ATR]
theorem twistedInverseImageBaseChangeMap_paste_horiz_app (sqR : IsPullback g f' f h)
    (sqL : IsPullback g' f'' f' h') (hR : TorIndependent f h) (hL : TorIndependent f' h')
    (K : quasiCoherentDerivedCategory Y) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz sqR sqL hR hL
    (twistedInverseImageBaseChangeMap (g' ≫ g) f'' f (h' ≫ h)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (g' ≫ g))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (h' ≫ h))
        (sqL.paste_horiz sqR)).app K =
      (quasiCoherentDerivedPullbackCompIso g' g).inv.app
          ((twistedInverseImage f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj K) ≫
        (quasiCoherentDerivedPullback' g').map
          ((torIndependentTwistedInverseImageBaseChange sqR hR).app K) ≫
        (torIndependentTwistedInverseImageBaseChange sqL hL).app
          ((quasiCoherentDerivedPullback' h).obj K) ≫
        (twistedInverseImage f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'')).map
          ((quasiCoherentDerivedPullbackCompIso h' h).hom.app K) := by
  have := isIso_twistedInverseImagePushforwardBaseChange_of_paste_horiz sqR sqL hR hL
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqR hR
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqL hL
  have := isIso_rightAdjointSquare_of_torIndependent sqR hR
  have := isIso_rightAdjointSquare_of_torIndependent sqL hL
  have := isIso_twoSquare_of_torIndependent sqR hR
  have := isIso_twoSquare_of_torIndependent sqL hL
  have := isIso_twoSquare_of_paste_horiz sqR sqL hR hL
  simp only [torIndependentTwistedInverseImageBaseChange]
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange (sqL.paste_horiz sqR),
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sqR,
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sqL]
  rw [Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq_of_paste
    (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (quasiCoherentDerivedAdjunction f' (isQuasicoherent_homology_derivedPullback' f')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (quasiCoherentDerivedAdjunction f'' (isQuasicoherent_homology_derivedPullback' f'')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
    (quasiCoherentDerivedPullbackCompIso f' h)
    (quasiCoherentDerivedPullbackCompIso g f ≪≫ quasiCoherentDerivedPullbackCongr sqR.w)
    (quasiCoherentDerivedPullbackCompIso f'' h')
    (quasiCoherentDerivedPullbackCompIso g' f' ≪≫ quasiCoherentDerivedPullbackCongr sqL.w)
    (quasiCoherentDerivedPullbackCompIso f'' (h' ≫ h))
    (quasiCoherentDerivedPullbackCompIso (g' ≫ g) f ≪≫
      quasiCoherentDerivedPullbackCongr (sqL.paste_horiz sqR).w)
    (quasiCoherentDerivedPullbackCongr (rfl : h' ≫ h = h' ≫ h).symm ≪≫
      (quasiCoherentDerivedPullbackCompIso h' h).symm)
    (quasiCoherentDerivedPullbackCompIso g' g ≪≫
      quasiCoherentDerivedPullbackCongr (rfl : g' ≫ g = g' ≫ g))
    (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
    (twistedInverseImageAdjunction f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f'))
    (twistedInverseImageAdjunction f'' (isQuasicoherent_homology_derivedPushforward_of_qcqs f''))
    (quasiCoherentDerivedAdjunction h (isQuasicoherent_homology_derivedPullback' h)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h))
    (quasiCoherentDerivedAdjunction h' (isQuasicoherent_homology_derivedPullback' h')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs h'))
    (quasiCoherentDerivedAdjunction (h' ≫ h) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedAdjunction g (isQuasicoherent_homology_derivedPullback' g)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g))
    (quasiCoherentDerivedAdjunction g' (isQuasicoherent_homology_derivedPullback' g')
      (isQuasicoherent_homology_derivedPushforward_of_qcqs g'))
    (quasiCoherentDerivedAdjunction (g' ≫ g) (isQuasicoherent_homology_derivedPullback' _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentPullbackComparisonPaste g f' f h g' f'' h' (g' ≫ g) (h' ≫ h) sqR.w sqL.w
      (sqL.paste_horiz sqR).w rfl rfl) K]
  simp only [Iso.trans_inv, Iso.symm_inv, quasiCoherentDerivedPullbackCongr_refl_inv,
    Category.id_comp, Category.comp_id]

end Stacks.Duality
