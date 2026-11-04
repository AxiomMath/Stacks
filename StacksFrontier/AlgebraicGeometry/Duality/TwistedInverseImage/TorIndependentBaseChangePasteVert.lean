module

public import
  StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.TorIndependentBaseChangePasteHoriz
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeTrace
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.PseudoFunctor

/-!
# The base change map of the twisted inverse image along two squares stacked vertically

Consider a commutative diagram

```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
|         |
g'        g
v         v
Z' --m--> Z
```

of quasi-compact and quasi-separated schemes in which both squares are cartesian, `f` and `l`
are Tor independent and `g` and `m` are Tor independent. Write `a, b, c` for the right adjoints
of `Rf_*, Rg_*, R(f ≫ g)_*` on `D_QCoh` ([Stacks, Tag 0A9E]) and `a', b', c'` for the primed
ones. The base change maps of [Stacks, Tag 0AA6] of the two squares compose to the base change
map of the outer rectangle ([Stacks, Tag 0ATQ]): for `K ∈ D_QCoh(𝒪_Z)`,

```
Lk^* c(K) ≅ Lk^* a(b(K)) ⟶ a'(Ll^* b(K)) ⟶ a'(b'(Lm^* K)) ≅ c'(Lm^* K),
```

the outer identifications being `c ≅ b ⋙ a` and `c' ≅ b' ⋙ a'` of [Stacks, Tag 0ATX].

The base change map of the outer rectangle is defined once its transformation
`ξ : Rk_* ∘ c' ⟶ c ∘ Rm_*` is invertible. This holds here because the derived base change map
`Lm^* ∘ R(f ≫ g)_* ⟶ R(f' ≫ g')_* ∘ Lk^*` of the rectangle is the vertical pasting of those of
the two squares, which are invertible by Tor independence ([Stacks, Tag 08IB]).

## Main results

* `Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert` — `ξ` of the
  outer rectangle is invertible.
* `Stacks.Duality.twistedInverseImageBaseChangeMap_paste_vert_app` — [Stacks, Tag 0ATQ].

## References

* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0ATL](https://stacks.math.columbia.edu/tag/0ATL)
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

variable {S T U S' T' U' : Type*} [Category S] [Category T] [Category U] [Category S']
  [Category T'] [Category U']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lh : T ⥤ U} {Rh : U ⥤ T} {Lo : S ⥤ U} {Ro : U ⥤ S}
  {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'} {Lh' : T' ⥤ U'} {Rh' : U' ⥤ T'} {Lo' : S' ⥤ U'}
  {Ro' : U' ⥤ S'}
  (adjf : Lf ⊣ Rf) (adjh : Lh ⊣ Rh) (adjo : Lo ⊣ Ro) (adjf' : Lf' ⊣ Rf') (adjh' : Lh' ⊣ Rh')
  (adjo' : Lo' ⊣ Ro')
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lk : U ⥤ U'} {Lc : S ⥤ T'} {Ld : T ⥤ U'} {Lco : S ⥤ U'}
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (eh : Lg' ⋙ Lh' ≅ Ld) (ek : Lh ⋙ Lk ≅ Ld)
  (ego : Lg ⋙ Lo' ≅ Lco) (efo : Lo ⋙ Lk ≅ Lco)
  (cL : Lf ⋙ Lh ≅ Lo) (cL' : Lf' ⋙ Lh' ≅ Lo') (cR : Rh ⋙ Rf ≅ Ro) (cR' : Rh' ⋙ Rf' ≅ Ro')

/-- **The base change map of pushforward along pullback around two squares stacked vertically is
invertible when those of the two squares are**, the outer one being their vertical pasting. -/
theorem isIso_twoSquare_of_pullbackComparison_vpaste
    (hpc : PullbackComparisonVPaste eg ef eh ek ego efo cL cL')
    (hR : CounitCompatible adjf adjh adjo cL cR) (hR' : CounitCompatible adjf' adjh' adjo' cL' cR')
    [IsIso (twoSquare adjf adjf' eg ef).natTrans] [IsIso (twoSquare adjh adjh' eh ek).natTrans] :
    IsIso (twoSquare adjo adjo' ego efo).natTrans := by
  have : ∀ M, IsIso ((twoSquare adjo adjo' ego efo).natTrans.app M) := fun M => by
    change IsIso (map adjo adjo' ego efo M)
    rw [map_eq_of_pullbackComparison_vpaste adjf adjh adjo adjf' adjh' adjo' eg ef eh ek ego efo
      cL cL' cR cR' hpc hR hR' M]
    have : IsIso (map adjf adjf' eg ef (Rh.obj M)) :=
      inferInstanceAs (IsIso ((twoSquare adjf adjf' eg ef).natTrans.app (Rh.obj M)))
    have : IsIso (map adjh adjh' eh ek M) :=
      inferInstanceAs (IsIso ((twoSquare adjh adjh' eh ek).natTrans.app M))
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end Stacks.CategoryTheory.BaseChange

namespace Stacks.Duality

variable {X' X Y' Y Z' Z : Scheme.{u}} [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z'] [QuasiSeparatedSpace Z']
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  {k : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {l : Y' ⟶ Y} {g' : Y' ⟶ Z'} {g : Y ⟶ Z}
  {m : Z' ⟶ Z}

/-- The derived base change map of the outer rectangle of two cartesian squares stacked
vertically, each Tor independent, is invertible: it is the vertical pasting of those of the two
squares. -/
theorem isIso_twoSquare_of_paste_vert (sqT : IsPullback k f' f l) (sqB : IsPullback l g' g m)
    (hT : TorIndependent f l) (hB : TorIndependent g m) :
    IsIso (Stacks.CategoryTheory.BaseChange.twoSquare
      (quasiCoherentDerivedAdjunction (f ≫ g) (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)))
      (quasiCoherentDerivedAdjunction (f' ≫ g') (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g')))
      (quasiCoherentDerivedPullbackCompIso (f' ≫ g') m)
      (quasiCoherentDerivedPullbackCompIso k (f ≫ g) ≪≫
        quasiCoherentDerivedPullbackCongr (sqT.paste_vert sqB).w)).natTrans := by
  have := isIso_twoSquare_of_torIndependent sqT hT
  have := isIso_twoSquare_of_torIndependent sqB hB
  exact Stacks.CategoryTheory.BaseChange.isIso_twoSquare_of_pullbackComparison_vpaste _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _
    (quasiCoherentPullbackComparisonVPaste k l m f g f' g' sqT.w sqB.w (sqT.paste_vert sqB).w)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f g)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f' g')

/-- **`ξ : Rk_* ∘ c' ⟶ c ∘ Rm_*` of the outer rectangle is invertible**, for two cartesian
squares of quasi-compact and quasi-separated schemes stacked vertically with `f`, `l` Tor
independent and `g`, `m` Tor independent; here `c`, `c'` are the right adjoints of
`R(f ≫ g)_*`, `R(f' ≫ g')_*`. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert
    (sqT : IsPullback k f' f l) (sqB : IsPullback l g' g m) (hT : TorIndependent f l)
    (hB : TorIndependent g m) :
    IsIso (twistedInverseImagePushforwardBaseChange k (f' ≫ g') (f ≫ g) m
      (isQuasicoherent_homology_derivedPushforward_of_qcqs k)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g'))
      (isQuasicoherent_homology_derivedPushforward_of_qcqs m) (sqT.paste_vert sqB)) := by
  have := isIso_twoSquare_of_paste_vert sqT sqB hT hB
  rw [twistedInverseImagePushforwardBaseChange_eq_rightAdjointSquare]
  exact Stacks.CategoryTheory.BaseChange.isIso_rightAdjointSquare _ _ _ _ _ _ _ _

/-- **[Stacks, Tag 0ATQ].** Consider a commutative diagram
```
X' --k--> X
|         |
f'        f
v         v
Y' --l--> Y
|         |
g'        g
v         v
Z' --m--> Z
```
of quasi-compact and quasi-separated schemes in which both squares are cartesian, `f` and `l`
are Tor independent and `g` and `m` are Tor independent. Then the base change maps
(Equation 48.5.0.1 of [Stacks, Tag 0AA6]) of the two squares compose to the base change map of
the outer rectangle: with `a`, `b`, `c` the right adjoints of `Rf_*`, `Rg_*`, `R(f ≫ g)_*` and
`a'`, `b'`, `c'` those of `Rf'_*`, `Rg'_*`, `R(f' ≫ g')_*`, for every `K ∈ D_QCoh(𝒪_Z)` the map
`Lk^* c(K) ⟶ c'(Lm^* K)` of the rectangle is

```
Lk^* c(K) = Lk^* a(b(K)) ⟶ a'(Ll^* b(K)) ⟶ a'(b'(Lm^* K)) = c'(Lm^* K),
```

the identifications `c = b ⋙ a` and `c' = b' ⋙ a'` being those of [Stacks, Tag 0ATX]
(`Stacks.Duality.twistedInverseImageCompIso`). The base change map of the rectangle is defined
because its `ξ` is invertible,
`Stacks.Duality.isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert`. -/
@[stacks 0ATQ]
theorem twistedInverseImageBaseChangeMap_paste_vert_app (sqT : IsPullback k f' f l)
    (sqB : IsPullback l g' g m) (hT : TorIndependent f l) (hB : TorIndependent g m)
    (K : quasiCoherentDerivedCategory Z) :
    haveI := isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert sqT sqB hT hB
    (twistedInverseImageBaseChangeMap k (f' ≫ g') (f ≫ g) m
        (isQuasicoherent_homology_derivedPushforward_of_qcqs k)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g'))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs m)
        (sqT.paste_vert sqB)).app K =
      (quasiCoherentDerivedPullback' k).map
          ((twistedInverseImageCompIso f g (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g))).hom.app K) ≫
        (torIndependentTwistedInverseImageBaseChange sqT hT).app
          ((twistedInverseImage g (isQuasicoherent_homology_derivedPushforward_of_qcqs g)).obj K) ≫
        (twistedInverseImage f' (isQuasicoherent_homology_derivedPushforward_of_qcqs f')).map
          ((torIndependentTwistedInverseImageBaseChange sqB hB).app K) ≫
        (twistedInverseImageCompIso f' g'
            (isQuasicoherent_homology_derivedPushforward_of_qcqs f')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs g')
            (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g'))).inv.app
          ((quasiCoherentDerivedPullback' m).obj K) := by
  have := isIso_twistedInverseImagePushforwardBaseChange_of_paste_vert sqT sqB hT hB
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqT hT
  have := isIso_twistedInverseImagePushforwardBaseChange_of_torIndependent sqB hB
  have := isIso_rightAdjointSquare_of_torIndependent sqT hT
  have := isIso_rightAdjointSquare_of_torIndependent sqB hB
  have := isIso_twoSquare_of_torIndependent sqT hT
  have := isIso_twoSquare_of_torIndependent sqB hB
  have := isIso_twoSquare_of_paste_vert sqT sqB hT hB
  have : IsIso (Stacks.CategoryTheory.BaseChange.rightAdjointSquare
      (quasiCoherentDerivedAdjunction (f ≫ g) (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)))
      (quasiCoherentDerivedAdjunction (f' ≫ g') (isQuasicoherent_homology_derivedPullback' _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g')))
      (quasiCoherentDerivedAdjunction m (isQuasicoherent_homology_derivedPullback' m)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs m))
      (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs k))
      (quasiCoherentDerivedPullbackCompIso (f' ≫ g') m)
      (quasiCoherentDerivedPullbackCompIso k (f ≫ g) ≪≫
        quasiCoherentDerivedPullbackCongr (sqT.paste_vert sqB).w)
      (twistedInverseImageAdjunction (f ≫ g)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f ≫ g)))
      (twistedInverseImageAdjunction (f' ≫ g')
        (isQuasicoherent_homology_derivedPushforward_of_qcqs (f' ≫ g')))).natTrans :=
    Stacks.CategoryTheory.BaseChange.isIso_rightAdjointSquare _ _ _ _ _ _ _ _
  simp only [torIndependentTwistedInverseImageBaseChange]
  rw [twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange (sqT.paste_vert sqB),
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sqT,
    twistedInverseImageBaseChangeMap_eq_rightAdjointBaseChange sqB]
  exact Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq_of_vpaste
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (quasiCoherentPullbackComparisonVPaste k l m f g f' g' sqT.w sqB.w (sqT.paste_vert sqB).w)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f g)
    (map_quasiCoherentDerivedPushforwardCompIso_comp_counit f' g')
    (map_twistedInverseImageCompIso_inv_comp_counit f g)
    (map_twistedInverseImageCompIso_inv_comp_counit f' g') K

end Stacks.Duality
